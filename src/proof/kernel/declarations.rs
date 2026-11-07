//! Invocation-local storage of declarations already checked by this kernel.
//! No receipt or persistent cache can insert a declaration. Before releasing a
//! checked object, compare its complete structure with the decoded scratch
//! representation. Later reads verify bytes against digests retained in RAM.
use super::{
    hash::Sha256,
    scratch::{Spool, DEFAULT_BYTES},
    Declaration, Family, Kernel, Result, T,
};
use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    sync::Arc,
};

#[path = "declaration_codec.rs"]
mod codec;

/// Store an arbitrary syntax root without introducing a checked declaration.
/// The empty envelope is only a codec container; it never enters the kernel.
pub(super) fn encode_term(value: &T) -> Result<Vec<u8>> {
    let envelope = Declaration {
        universes: vec![],
        ty: value.clone(),
        value: None,
        family: None,
    };
    // Bound the encoder's temporary DAG traversal as well as its output.
    codec::weight(&envelope)?;
    let bytes = codec::encode(&envelope)?;
    let decoded = codec::decode(&bytes)?;
    if !same_declaration(&envelope, &decoded)? {
        return Err("syntax scratch round-trip mismatch".into());
    }
    Ok(bytes)
}

pub(super) fn decode_term(bytes: &[u8]) -> Result<T> {
    let envelope = codec::decode(bytes)?;
    if !envelope.universes.is_empty() || envelope.value.is_some() || envelope.family.is_some() {
        return Err("invalid syntax scratch envelope".into());
    }
    Ok(envelope.ty)
}

pub(super) fn term_weight(
    value: &T,
    limit: usize,
    meter: &mut impl FnMut(usize) -> Result<()>,
) -> Result<Option<(usize, usize)>> {
    codec::term_weight(value, limit, meter)
}

const RESIDENT_BYTES: usize = 8 * 1024 * 1024;
const MAX_BLOB_BYTES: usize = 32 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Blob {
    offset: u64,
    bytes: usize,
    digest: [u8; 32],
}
#[path = "declaration_directory.rs"]
mod directory;
use directory::Directory;

struct Entry {
    value: Arc<Declaration>,
    bytes: Option<usize>,
}
pub(super) struct Declarations {
    // Only active resident values live here. Completed cold names and blob
    // references move to the independently bounded directory.
    entries: HashMap<String, Entry>,
    stored: Directory,
    pending: Vec<String>,
    order: VecDeque<String>,
    resident_bytes: usize,
    limit: Option<usize>,
    cold: RefCell<Cold>,
    poisoned: std::cell::Cell<bool>,
}
struct Cold {
    spool: Option<Spool>,
    blobs: Directory,
    cache: HashMap<String, (Arc<Declaration>, usize)>,
    order: VecDeque<String>,
    bytes: usize,
    poisoned: bool,
    scratch_limit: u64,
}

impl Default for Cold {
    fn default() -> Self {
        Self::with_scratch_limit(DEFAULT_BYTES)
    }
}
impl Cold {
    fn with_scratch_limit(scratch_limit: u64) -> Self {
        Self {
            spool: None,
            blobs: Directory::with_scratch_limit(scratch_limit),
            cache: HashMap::new(),
            order: VecDeque::new(),
            bytes: 0,
            poisoned: false,
            scratch_limit,
        }
    }
}

impl Declarations {
    pub(super) fn new() -> Self {
        Self::with_scratch_limit(DEFAULT_BYTES)
    }
    pub(super) fn with_scratch_limit(max_file_bytes: u64) -> Self {
        Self {
            entries: HashMap::new(),
            stored: Directory::with_scratch_limit(max_file_bytes),
            pending: vec![],
            order: VecDeque::new(),
            resident_bytes: 0,
            limit: None,
            cold: RefCell::new(Cold::with_scratch_limit(max_file_bytes)),
            poisoned: std::cell::Cell::new(false),
        }
    }
    pub(super) fn enable_spilling(&mut self) {
        self.enable_with_limit(RESIDENT_BYTES);
    }
    fn enable_with_limit(&mut self, limit: usize) {
        if self.limit.is_none() {
            let mut names = self.entries.keys().cloned().collect::<Vec<_>>();
            names.sort();
            self.pending = names.clone();
            self.order = names.into();
        }
        self.limit = Some(limit);
    }
    #[cfg(test)]
    pub(super) fn set_limit(&mut self, limit: usize) {
        self.enable_with_limit(limit);
        self.stored.set_limit(limit);
        self.cold.get_mut().blobs.set_limit(limit);
    }
    #[cfg(test)]
    pub(super) fn directories_spilled(&self) -> bool {
        self.stored.is_spilled() && self.cold.borrow().blobs.is_spilled()
    }
    #[cfg(test)]
    pub(super) fn resident_value_bytes(&self) -> usize {
        self.resident_bytes + self.cold.borrow().bytes
    }
    #[cfg(test)]
    pub(super) fn corrupt_stored_value(&mut self, name: &str) -> Result<()> {
        let blob = self
            .stored
            .get(name.as_bytes())?
            .ok_or("missing cold test declaration")?;
        let cold = self.cold.get_mut();
        cold.cache.clear();
        cold.order.clear();
        cold.bytes = 0;
        let spool = cold.spool.as_mut().ok_or("missing cold test scratch")?;
        // Flush even a small pending record before corrupting its protected
        // bytes. The next lookup must observe the original page digest.
        spool.append(&[0; 64 * 1024])?;
        spool.overwrite_flushed(blob.offset, b"!")
    }
    fn healthy(&self) -> Result<()> {
        if self.poisoned.get() {
            return Err("kernel declaration storage is invalid after a storage error".into());
        }
        self.stored.healthy()?;
        self.cold.borrow().healthy()
    }
    fn checked<T>(&self, result: Result<T>) -> Result<T> {
        if result.is_err() {
            self.poisoned.set(true);
        }
        result
    }
    pub(super) fn contains_key(&self, name: &str) -> Result<bool> {
        self.healthy()?;
        if self.entries.contains_key(name) || self.cold.borrow().cache.contains_key(name) {
            return Ok(true);
        }
        self.checked(
            self.stored
                .get(name.as_bytes())
                .map(|entry| entry.is_some()),
        )
    }
    /// An optional scheduling hint; never page in a declaration just to obtain
    /// it. Ordinary source checking and conversion still validate every term.
    pub(super) fn resident(&self, name: &str) -> Result<Option<Arc<Declaration>>> {
        self.healthy()?;
        if let Some(entry) = self.entries.get(name) {
            return Ok(Some(entry.value.clone()));
        }
        Ok(self
            .cold
            .borrow()
            .cache
            .get(name)
            .map(|(declaration, _)| declaration.clone()))
    }
    pub(super) fn get(&self, name: &str) -> Result<Option<Arc<Declaration>>> {
        self.healthy()?;
        if let Some(entry) = self.entries.get(name) {
            return Ok(Some(entry.value.clone()));
        }
        if let Some(value) = self.cold.borrow_mut().cached(name) {
            return Ok(Some(value));
        }
        let result = (|| {
            let Some(blob) = self.stored.get(name.as_bytes())? else {
                return Ok(None);
            };
            self.cold
                .borrow_mut()
                .load(
                    name,
                    blob,
                    self.limit.unwrap_or(0).saturating_sub(self.resident_bytes),
                )
                .map(Some)
        })();
        self.checked(result)
    }
    pub(super) fn get_mut(&mut self, name: &str) -> Result<Option<&mut Declaration>> {
        self.healthy()?;
        if !self.entries.contains_key(name) {
            let Some(value) = self.get(name)? else {
                return Ok(None);
            };
            self.remove(name)?;
            self.insert(name.to_owned(), value.as_ref().clone())?;
        }
        if let Some(entry) = self.entries.get_mut(name) {
            if let Some(bytes) = entry.bytes.take() {
                self.resident_bytes -= bytes;
                self.pending.push(name.to_owned());
            }
        }
        Ok(self
            .entries
            .get_mut(name)
            .map(|entry| Arc::make_mut(&mut entry.value)))
    }
    pub(super) fn insert(&mut self, name: String, value: Declaration) -> Result<()> {
        self.healthy()?;
        self.remove(&name)?;
        if self.limit.is_some() {
            self.pending.push(name.clone());
            self.order.push_back(name.clone());
        }
        self.entries.insert(
            name,
            Entry {
                value: Arc::new(value),
                bytes: None,
            },
        );
        Ok(())
    }
    pub(super) fn remove(&mut self, name: &str) -> Result<()> {
        self.healthy()?;
        if let Some(entry) = self.entries.remove(name) {
            if let Some(bytes) = entry.bytes {
                self.resident_bytes -= bytes;
            }
            self.pending.retain(|key| key != name);
            self.order.retain(|key| key != name);
        } else {
            let result = self.stored.set(name.as_bytes(), None);
            self.checked(result)?;
        }
        self.cold.get_mut().remove_cached(name);
        Ok(())
    }
    /// Call only after a whole declaration/group has successfully checked.
    /// The boolean signals that old expression Weak handles may now be dead.
    pub(super) fn trim(&mut self) -> Result<bool> {
        self.healthy()?;
        let result = self.trim_inner();
        self.checked(result)
    }
    fn trim_inner(&mut self) -> Result<bool> {
        let Some(limit) = self.limit else {
            return Ok(false);
        };
        for name in std::mem::take(&mut self.pending) {
            if let Some((key, entry)) = self.entries.get_key_value(&name) {
                if entry.bytes.is_none() {
                    let weight = resident_weight(key, &entry.value)?;
                    self.resident_bytes = self
                        .resident_bytes
                        .checked_add(weight)
                        .ok_or("kernel declaration storage accounting overflow")?;
                    self.entries.get_mut(&name).unwrap().bytes = Some(weight);
                }
            }
        }
        self.cold
            .get_mut()
            .trim(limit.saturating_sub(self.resident_bytes));
        if self.resident_bytes <= limit {
            return Ok(false);
        }
        let target = limit / 2;
        let mut evicted = false;
        while self.resident_bytes > target {
            let name = self
                .order
                .pop_front()
                .ok_or("missing resident declaration index")?;
            let Some(entry) = self.entries.get(&name) else {
                continue;
            };
            let weight = entry.bytes.ok_or("unaccounted resident declaration")?;
            let blob = self.cold.get_mut().store(&entry.value)?;
            self.stored.set(name.as_bytes(), Some(blob))?;
            self.entries.remove(&name);
            self.resident_bytes -= weight;
            evicted = true;
        }
        if self.entries.is_empty() {
            self.entries.shrink_to_fit();
            self.order.shrink_to_fit();
        }
        Ok(evicted)
    }
}

fn resident_weight(name: &String, value: &Declaration) -> Result<usize> {
    // Include both name copies and conservative spare map/queue metadata,
    // rather than allowing tiny values with large names to evade the budget.
    codec::weight(value)?
        .checked_add(name.capacity())
        .and_then(|n| n.checked_add(name.len()))
        .and_then(|n| {
            n.checked_add(
                4 * std::mem::size_of::<(String, Entry)>() + 2 * std::mem::size_of::<String>(),
            )
        })
        .ok_or_else(|| "kernel declaration storage accounting overflow".into())
}
fn cache_weight(name: &str, value: &Declaration) -> Result<usize> {
    codec::weight(value)?
        .checked_add(name.len().saturating_mul(2))
        .and_then(|n| {
            n.checked_add(
                4 * std::mem::size_of::<(String, (Arc<Declaration>, usize))>()
                    + 2 * std::mem::size_of::<String>(),
            )
        })
        .ok_or_else(|| "kernel declaration cache accounting overflow".into())
}

impl Cold {
    fn healthy(&self) -> Result<()> {
        if self.poisoned {
            Err("kernel declaration scratch storage is invalid".into())
        } else {
            self.blobs.healthy()
        }
    }
    fn cached(&mut self, name: &str) -> Option<Arc<Declaration>> {
        let value = self.cache.get(name)?.0.clone();
        self.order.retain(|item| item != name);
        self.order.push_back(name.to_owned());
        Some(value)
    }
    fn remove_cached(&mut self, name: &str) {
        if let Some((_, bytes)) = self.cache.remove(name) {
            self.bytes -= bytes;
            self.order.retain(|item| item != name);
        }
    }
    fn trim(&mut self, limit: usize) {
        while self.bytes > limit {
            let Some(name) = self.order.pop_front() else {
                break;
            };
            if let Some((_, bytes)) = self.cache.remove(&name) {
                self.bytes -= bytes;
            }
        }
    }
    fn read(&mut self, blob: Blob) -> Result<Vec<u8>> {
        self.healthy()?;
        let result = (|| {
            if blob.bytes > MAX_BLOB_BYTES {
                return Err("kernel declaration scratch record limit exceeded".into());
            }
            let spool = self
                .spool
                .as_mut()
                .ok_or("missing kernel declaration scratch file")?;
            if blob
                .offset
                .checked_add(blob.bytes as u64)
                .is_none_or(|end| end > spool.len())
            {
                return Err("kernel declaration scratch record range is invalid".into());
            }
            let mut bytes = vec![0; blob.bytes];
            for (index, chunk) in bytes.chunks_mut(64 * 1024).enumerate() {
                spool.read_into(blob.offset + (index * 64 * 1024) as u64, chunk)?;
            }
            if digest(&bytes) != blob.digest {
                return Err("kernel declaration scratch record checksum mismatch".into());
            }
            Ok(bytes)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }
    fn store(&mut self, value: &Declaration) -> Result<Blob> {
        self.healthy()?;
        let bytes = codec::encode(value)?;
        if bytes.len() > MAX_BLOB_BYTES {
            return Err("kernel declaration scratch record limit exceeded".into());
        }
        let decoded = codec::decode(&bytes)?;
        if !same_declaration(value, &decoded)? {
            return Err("kernel declaration scratch round-trip mismatch".into());
        }
        let digest = digest(&bytes);
        if let Some(blob) = self.blobs.get(&digest)? {
            if self.read(blob)? != bytes {
                return Err("kernel declaration scratch digest collision".into());
            }
            return Ok(blob);
        }
        if self.spool.is_none() {
            self.spool = Some(Spool::with_limit(self.scratch_limit)?);
        }
        let offset = self
            .spool
            .as_mut()
            .ok_or("missing kernel declaration scratch file")?
            .append(&bytes)?;
        let blob = Blob {
            offset,
            bytes: bytes.len(),
            digest,
        };
        self.blobs.set(&digest, Some(blob))?;
        Ok(blob)
    }
    fn load(&mut self, name: &str, blob: Blob, limit: usize) -> Result<Arc<Declaration>> {
        self.healthy()?;
        if let Some(value) = self.cached(name) {
            return Ok(value);
        }
        let bytes = self.read(blob)?;
        let decoded = codec::decode(&bytes);
        if decoded.is_err() {
            self.poisoned = true;
        }
        let value = Arc::new(decoded?);
        let weight = cache_weight(name, &value)?;
        self.trim(limit.saturating_sub(weight));
        if weight <= limit {
            self.bytes += weight;
            self.order.push_back(name.to_owned());
            self.cache.insert(name.to_owned(), (value.clone(), weight));
        }
        Ok(value)
    }
}

fn digest(bytes: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(bytes);
    hash.finish()
}

/// Independent structural comparison, not encode(decode(bytes)) equality.
fn same_declaration(a: &Declaration, b: &Declaration) -> Result<bool> {
    let mut kernel = Kernel::with_budget(crate::ProofBudget::default());
    fn terms(kernel: &mut Kernel, a: &[T], b: &[T]) -> Result<bool> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            kernel.reset_budget();
            if !kernel.same_syntax(a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn family(kernel: &mut Kernel, a: &Family, b: &Family) -> Result<bool> {
        if a.group != b.group
            || a.sort != b.sort
            || a.large != b.large
            || a.constructors.len() != b.constructors.len()
            || !terms(kernel, &a.parameters, &b.parameters)?
            || !terms(kernel, &a.indices, &b.indices)?
        {
            return Ok(false);
        }
        for (a, b) in a.constructors.iter().zip(&b.constructors) {
            if a.name != b.name
                || a.recursive != b.recursive
                || !terms(kernel, &a.fields, &b.fields)?
                || !terms(kernel, &a.result_indices, &b.result_indices)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
    if a.universes != b.universes
        || !terms(
            &mut kernel,
            std::slice::from_ref(&a.ty),
            std::slice::from_ref(&b.ty),
        )?
    {
        return Ok(false);
    }
    match (&a.value, &b.value) {
        (None, None) => (),
        (Some(a), Some(b))
            if terms(
                &mut kernel,
                std::slice::from_ref(a),
                std::slice::from_ref(b),
            )? =>
        {
            ()
        }
        _ => return Ok(false),
    }
    match (&a.family, &b.family) {
        (None, None) => Ok(true),
        (Some(a), Some(b)) => family(&mut kernel, a, b),
        _ => Ok(false),
    }
}

#[cfg(test)]
#[path = "declarations_tests.rs"]
mod tests;
