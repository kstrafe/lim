//! Invocation-local storage of declarations already checked by this kernel.
//! No receipt or persistent cache can insert a declaration. Before releasing a
//! checked object, compare its complete structure with the decoded scratch
//! representation. Later reads verify bytes against digests retained in RAM.
use super::{hash::Sha256, scratch::Spool, Declaration, Family, Kernel, Result, T};
use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    sync::Arc,
};

#[path = "declaration_codec.rs"]
mod codec;

const RESIDENT_BYTES: usize = 8 * 1024 * 1024;
const MAX_BLOB_BYTES: usize = 32 * 1024 * 1024;

#[derive(Clone, Copy)]
struct Blob {
    offset: u64,
    bytes: usize,
    digest: [u8; 32],
}
enum Entry {
    Resident {
        value: Arc<Declaration>,
        bytes: Option<usize>,
    },
    Stored(Blob),
}
pub(super) struct Declarations {
    entries: HashMap<String, Entry>,
    pending: Vec<String>,
    order: VecDeque<String>,
    resident_bytes: usize,
    limit: Option<usize>,
    cold: RefCell<Cold>,
}
#[derive(Default)]
struct Cold {
    spool: Option<Spool>,
    blobs: HashMap<[u8; 32], Blob>,
    cache: HashMap<String, (Arc<Declaration>, usize)>,
    order: VecDeque<String>,
    bytes: usize,
    poisoned: bool,
}

impl Declarations {
    pub(super) fn new() -> Self {
        Self {
            entries: HashMap::new(),
            pending: vec![],
            order: VecDeque::new(),
            resident_bytes: 0,
            limit: None,
            cold: RefCell::new(Cold::default()),
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
    }
    pub(super) fn contains_key(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }
    pub(super) fn get(&self, name: &str) -> Result<Option<Arc<Declaration>>> {
        self.cold.borrow().healthy()?;
        match self.entries.get(name) {
            None => Ok(None),
            Some(Entry::Resident { value, .. }) => Ok(Some(value.clone())),
            Some(Entry::Stored(blob)) => self
                .cold
                .borrow_mut()
                .load(
                    name,
                    *blob,
                    self.limit.unwrap_or(0).saturating_sub(self.resident_bytes),
                )
                .map(Some),
        }
    }
    pub(super) fn get_mut(&mut self, name: &str) -> Result<Option<&mut Declaration>> {
        self.cold.get_mut().healthy()?;
        if matches!(self.entries.get(name), Some(Entry::Stored(_))) {
            let value = self.get(name)?.ok_or("missing stored kernel declaration")?;
            self.remove(name);
            self.insert(name.to_owned(), value.as_ref().clone());
        }
        // Mutation is used for provisional inductives and opaque initializers.
        // It invalidates the old stored representation before returning access.
        if let Some(Entry::Resident { bytes, .. }) = self.entries.get_mut(name) {
            if let Some(bytes) = bytes.take() {
                self.resident_bytes -= bytes;
                self.pending.push(name.to_owned());
            }
        }
        let Some(Entry::Resident { value, .. }) = self.entries.get_mut(name) else {
            return Ok(None);
        };
        Ok(Some(Arc::make_mut(value)))
    }
    pub(super) fn insert(&mut self, name: String, value: Declaration) {
        self.remove(&name);
        if self.limit.is_some() {
            self.pending.push(name.clone());
            self.order.push_back(name.clone());
        }
        self.entries.insert(
            name,
            Entry::Resident {
                value: Arc::new(value),
                bytes: None,
            },
        );
    }
    pub(super) fn remove(&mut self, name: &str) {
        if let Some(Entry::Resident {
            bytes: Some(bytes), ..
        }) = self.entries.remove(name)
        {
            self.resident_bytes -= bytes;
        }
        self.cold.get_mut().remove_cached(name);
    }
    /// Call only after a whole declaration/group has successfully checked.
    /// The boolean signals that old expression Weak handles may now be dead.
    pub(super) fn trim(&mut self) -> Result<bool> {
        let Some(limit) = self.limit else {
            return Ok(false);
        };
        self.cold.get_mut().healthy()?;
        for name in std::mem::take(&mut self.pending) {
            if let Some(Entry::Resident { value, bytes }) = self.entries.get_mut(&name) {
                if bytes.is_none() {
                    let weight = codec::weight(value)?;
                    self.resident_bytes = self
                        .resident_bytes
                        .checked_add(weight)
                        .ok_or("kernel declaration storage accounting overflow")?;
                    *bytes = Some(weight);
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
            let Some(Entry::Resident {
                value,
                bytes: Some(weight),
            }) = self.entries.get(&name)
            else {
                continue;
            };
            let weight = *weight;
            let blob = self.cold.get_mut().store(value)?;
            self.entries.insert(name, Entry::Stored(blob));
            self.resident_bytes -= weight;
            evicted = true;
        }
        Ok(evicted)
    }
}

impl Cold {
    fn healthy(&self) -> Result<()> {
        if self.poisoned {
            Err("kernel declaration scratch storage is invalid".into())
        } else {
            Ok(())
        }
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
        if let Some(blob) = self.blobs.get(&digest).copied() {
            if self.read(blob)? != bytes {
                return Err("kernel declaration scratch digest collision".into());
            }
            return Ok(blob);
        }
        if self.spool.is_none() {
            self.spool = Some(Spool::new()?);
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
        self.blobs.insert(digest, blob);
        Ok(blob)
    }
    fn load(&mut self, name: &str, blob: Blob, limit: usize) -> Result<Arc<Declaration>> {
        self.healthy()?;
        if let Some((value, _)) = self.cache.get(name) {
            let value = value.clone();
            self.order.retain(|item| item != name);
            self.order.push_back(name.to_owned());
            return Ok(value);
        }
        let bytes = self.read(blob)?;
        let decoded = codec::decode(&bytes);
        if decoded.is_err() {
            self.poisoned = true;
        }
        let value = Arc::new(decoded?);
        let weight = codec::weight(&value)?;
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
