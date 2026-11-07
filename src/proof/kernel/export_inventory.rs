//! Bounded storage for accepted declaration reports.
use super::{spool::Spool, LeanDeclarationReport, Result};
use std::{borrow::Cow, cell::RefCell};

const MEMORY_BYTES: usize = 1024 * 1024;
const INDEX_BYTES: usize = 16;
const MAX_PART: usize = 16_384;
const MAX_KIND: usize = 32;
const MAX_HASH: usize = 64;
const MAX_RECORD: usize = super::MAX_NAME_BYTES + 65_536;
const PAGE: usize = 64 * 1024;

pub(super) struct Inventory(Storage, usize, u64);
enum Storage {
    Memory {
        values: Vec<LeanDeclarationReport>,
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

impl Inventory {
    pub(super) fn new() -> Self {
        Self::with_limit(MEMORY_BYTES)
    }
    pub(super) fn with_limit(limit: usize) -> Self {
        Self::build(
            limit,
            super::MAX_DECLARATIONS,
            super::scratch::DEFAULT_BYTES,
        )
    }
    pub(super) fn with_limits(max_count: usize, max_scratch_bytes: u64) -> Self {
        Self::build(MEMORY_BYTES, max_count, max_scratch_bytes)
    }
    pub(super) fn with_count_limit(max_count: usize) -> Self {
        if max_count == super::MAX_DECLARATIONS {
            Self::new()
        } else {
            Self::build(MEMORY_BYTES, max_count, super::scratch::DEFAULT_BYTES)
        }
    }
    fn build(limit: usize, max_count: usize, scratch_limit: u64) -> Self {
        Self(
            Storage::Memory {
                values: Vec::new(),
                bytes: 0,
                limit,
            },
            max_count,
            scratch_limit,
        )
    }
    pub(super) fn len(&self) -> usize {
        match &self.0 {
            Storage::Memory { values, .. } => values.len(),
            Storage::Spilled(s) => s.count,
        }
    }
    pub(super) fn get(&self, id: usize) -> Result<Cow<'_, LeanDeclarationReport>> {
        match &self.0 {
            Storage::Memory { values, .. } => values
                .get(id)
                .map(Cow::Borrowed)
                .ok_or_else(reference_error),
            Storage::Spilled(s) => s.get(id).map(Cow::Owned),
        }
    }
    /// Compare only the exact canonical key for a candidate declaration.
    /// This avoids rebuilding its dependency list for membership lookups.
    pub(super) fn matches_identity(&self, id: usize, key: &str) -> Result<bool> {
        match &self.0 {
            Storage::Memory { values, .. } => values
                .get(id)
                .map(|value| value.identity == key)
                .ok_or_else(reference_error),
            Storage::Spilled(s) => s.matches_identity(id, key),
        }
    }
    /// Return the bounded display name and canonical identity without decoding
    /// the remainder of a spilled declaration record.
    pub(super) fn name_identity(&self, id: usize) -> Result<(String, String)> {
        match &self.0 {
            Storage::Memory { values, .. } => values
                .get(id)
                .map(|value| (value.name.clone(), value.identity.clone()))
                .ok_or_else(reference_error),
            Storage::Spilled(s) => s.name_identity(id),
        }
    }
    pub(super) fn push(&mut self, report: LeanDeclarationReport) -> Result<()> {
        validate(&report)?;
        if self.len() >= self.1 {
            return Err("declaration report count limit exceeded".into());
        }
        if let Storage::Memory {
            values,
            bytes,
            limit,
        } = &mut self.0
        {
            let owned = memory_weight(&report)?;
            let capacity = if values.len() == values.capacity() {
                values
                    .capacity()
                    .checked_mul(2)
                    .unwrap_or(usize::MAX)
                    .max(4)
            } else {
                values.capacity()
            };
            let projected = capacity
                .checked_mul(std::mem::size_of::<LeanDeclarationReport>())
                .and_then(|n| n.checked_add(*bytes))
                .and_then(|n| n.checked_add(owned));
            if projected.is_some_and(|n| n <= *limit) {
                *bytes = bytes
                    .checked_add(owned)
                    .ok_or("report memory size overflow")?;
                values.push(report);
                return Ok(());
            }
            let mut spilled = Spilled {
                index: RefCell::new(Spool::with_limit(self.2)?),
                data: RefCell::new(Spool::with_limit(self.2)?),
                count: 0,
            };
            for value in values.iter() {
                spilled.push(value)?;
            }
            self.0 = Storage::Spilled(spilled);
        }
        let Storage::Spilled(spilled) = &mut self.0 else {
            return Err("invalid declaration inventory state".into());
        };
        spilled.push(&report)
    }
    pub(super) fn into_vec(self) -> Result<Vec<LeanDeclarationReport>> {
        match self.0 {
            Storage::Memory { values, .. } => Ok(values),
            Storage::Spilled(s) => (0..s.count).map(|i| s.get(i)).collect(),
        }
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.0, Storage::Spilled(_))
    }
}

impl Spilled {
    fn push(&mut self, value: &LeanDeclarationReport) -> Result<()> {
        let bytes = encode(value)?;
        if decode(&bytes)? != *value {
            return Err("declaration report scratch round-trip mismatch".into());
        }
        let offset = self.data.get_mut().append(&bytes)?;
        let mut index = [0u8; INDEX_BYTES];
        index[..8].copy_from_slice(&offset.to_le_bytes());
        index[8..].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
        let expected = (self.count as u64)
            .checked_mul(INDEX_BYTES as u64)
            .ok_or("declaration index overflow")?;
        if self.index.get_mut().append(&index)? != expected {
            return Err("declaration report index is not contiguous".into());
        }
        self.count = self
            .count
            .checked_add(1)
            .ok_or("declaration report count overflow")?;
        Ok(())
    }
    fn meta(&self, id: usize) -> Result<(u64, usize)> {
        if id >= self.count {
            return Err(reference_error());
        }
        let offset = u64::try_from(id)
            .map_err(|_| "declaration index overflow")?
            .checked_mul(INDEX_BYTES as u64)
            .ok_or("declaration index overflow")?;
        let mut index = [0; INDEX_BYTES];
        self.index.borrow_mut().read_into(offset, &mut index)?;
        let start = u64::from_le_bytes(
            index[..8]
                .try_into()
                .map_err(|_| "invalid declaration index")?,
        );
        let len64 = u64::from_le_bytes(
            index[8..]
                .try_into()
                .map_err(|_| "invalid declaration index")?,
        );
        let len = usize::try_from(len64).map_err(|_| "invalid declaration record length")?;
        if !(1..=MAX_RECORD).contains(&len)
            || start
                .checked_add(len64)
                .is_none_or(|end| end > self.data.borrow().len())
        {
            return Err("invalid declaration report index record".into());
        }
        Ok((start, len))
    }
    fn get(&self, id: usize) -> Result<LeanDeclarationReport> {
        let (start, len) = self.meta(id)?;
        let mut bytes = vec![0; len];
        for (i, chunk) in bytes.chunks_mut(PAGE).enumerate() {
            let off = start
                .checked_add(
                    u64::try_from(i.checked_mul(PAGE).ok_or("declaration offset overflow")?)
                        .map_err(|_| "declaration offset overflow")?,
                )
                .ok_or("declaration offset overflow")?;
            self.data.borrow_mut().read_into(off, chunk)?;
        }
        decode(&bytes)
    }
    fn matches_identity(&self, id: usize, key: &str) -> Result<bool> {
        let (start, len) = self.meta(id)?;
        let mut data = self.data.borrow_mut();
        let mut field = [0; 4];
        if len < 4 {
            return Err("truncated declaration report name".into());
        }
        data.read_into(start, &mut field)?;
        let name_len = u32::from_le_bytes(field) as usize;
        let identity_length_at = 4usize
            .checked_add(name_len)
            .filter(|at| name_len <= MAX_PART && at.checked_add(4).is_some_and(|end| end <= len))
            .ok_or("invalid declaration report name length")?;
        data.read_into(start + identity_length_at as u64, &mut field)?;
        let identity_len = u32::from_le_bytes(field) as usize;
        let identity_at = identity_length_at + 4;
        if identity_len > MAX_PART
            || identity_at
                .checked_add(identity_len)
                .is_none_or(|end| end > len)
        {
            return Err("invalid declaration report identity length".into());
        }
        if identity_len != key.len() {
            return Ok(false);
        }
        // Metadata already bounded this complete range inside the data file.
        // Reading through Spool retains current-invocation page protection.
        let mut buffer = [0; 512];
        let mut at = start + identity_at as u64;
        for part in key.as_bytes().chunks(buffer.len()) {
            data.read_into(at, &mut buffer[..part.len()])?;
            if &buffer[..part.len()] != part {
                return Ok(false);
            }
            at += part.len() as u64;
        }
        Ok(true)
    }
    fn name_identity(&self, id: usize) -> Result<(String, String)> {
        let (start, len) = self.meta(id)?;
        let mut data = self.data.borrow_mut();
        let (name, identity_at) = read_part(&mut data, start, len, 0, "name")?;
        let (identity, _) = read_part(&mut data, start, len, identity_at, "identity")?;
        Ok((name, identity))
    }
}

/// Read one bounded length-prefixed UTF-8 field from a metadata-validated
/// record. All payload bytes go through Spool so page protection is retained.
fn read_part(
    data: &mut Spool,
    start: u64,
    record_len: usize,
    prefix_at: usize,
    label: &str,
) -> Result<(String, usize)> {
    let prefix_end = prefix_at
        .checked_add(4)
        .filter(|end| *end <= record_len)
        .ok_or_else(|| format!("truncated declaration report {label}"))?;
    let prefix_offset = start
        .checked_add(u64::try_from(prefix_at).map_err(|_| "declaration offset overflow")?)
        .ok_or("declaration offset overflow")?;
    let mut prefix = [0u8; 4];
    data.read_into(prefix_offset, &mut prefix)?;
    let len = u32::from_le_bytes(prefix) as usize;
    let end = prefix_end
        .checked_add(len)
        .filter(|end| len <= MAX_PART && *end <= record_len)
        .ok_or_else(|| format!("invalid declaration report {label} length"))?;
    let payload_offset = start
        .checked_add(u64::try_from(prefix_end).map_err(|_| "declaration offset overflow")?)
        .ok_or("declaration offset overflow")?;
    let payload_end = payload_offset
        .checked_add(u64::try_from(len).map_err(|_| "declaration offset overflow")?)
        .ok_or("declaration offset overflow")?;
    if payload_end
        > start
            .checked_add(record_len as u64)
            .ok_or("declaration offset overflow")?
    {
        return Err(format!("invalid declaration report {label} range").into());
    }
    let mut bytes = vec![0; len];
    for (i, chunk) in bytes.chunks_mut(PAGE).enumerate() {
        let offset = payload_offset
            .checked_add(
                u64::try_from(i.checked_mul(PAGE).ok_or("declaration offset overflow")?)
                    .map_err(|_| "declaration offset overflow")?,
            )
            .ok_or("declaration offset overflow")?;
        data.read_into(offset, chunk)?;
    }
    let value = String::from_utf8(bytes).map_err(|_| "invalid declaration report UTF-8")?;
    Ok((value, end))
}

fn reference_error() -> String {
    "invalid declaration report index".into()
}
fn memory_weight(r: &LeanDeclarationReport) -> Result<usize> {
    let mut n = 0usize;
    for s in [&r.name, &r.identity, &r.kind, &r.sha256] {
        n = n
            .checked_add(s.capacity())
            .ok_or("declaration memory size overflow")?;
    }
    n = n
        .checked_add(
            r.dependencies
                .capacity()
                .checked_mul(std::mem::size_of::<String>())
                .ok_or("declaration memory size overflow")?,
        )
        .ok_or("declaration memory size overflow")?;
    for s in &r.dependencies {
        n = n
            .checked_add(s.capacity())
            .ok_or("declaration memory size overflow")?;
    }
    Ok(n)
}
fn validate(r: &LeanDeclarationReport) -> Result<()> {
    if r.name.len() > MAX_PART
        || r.identity.len() > MAX_PART
        || r.kind.len() > MAX_KIND
        || r.sha256.len() != MAX_HASH
        || !r
            .sha256
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        || r.line == 0
        || r.dependencies.len() > super::MAX_DEPENDENCIES
    {
        return Err("invalid declaration report field or limit".into());
    }
    let mut weight = 0usize;
    for s in &r.dependencies {
        if s.len() > MAX_PART {
            return Err("declaration dependency string limit exceeded".into());
        }
        weight = weight
            .checked_add(s.len())
            .and_then(|v| v.checked_add(32))
            .filter(|v| *v <= super::MAX_NAME_BYTES)
            .ok_or("declaration dependency byte limit exceeded")?;
    }
    if encode_len(r)? > MAX_RECORD {
        return Err("declaration report record byte limit exceeded".into());
    }
    Ok(())
}
fn encode_len(r: &LeanDeclarationReport) -> Result<usize> {
    let mut n = 8usize
        .checked_add(4)
        .ok_or("declaration record size overflow")?;
    for s in [&r.name, &r.identity, &r.kind, &r.sha256] {
        n = n
            .checked_add(4 + s.len())
            .ok_or("declaration record size overflow")?;
    }
    for s in &r.dependencies {
        n = n
            .checked_add(4 + s.len())
            .ok_or("declaration record size overflow")?;
    }
    Ok(n)
}
fn encode(r: &LeanDeclarationReport) -> Result<Vec<u8>> {
    validate(r)?;
    let mut b = Vec::with_capacity(encode_len(r)?);
    b.extend_from_slice(&(r.name.len() as u32).to_le_bytes());
    b.extend_from_slice(r.name.as_bytes());
    b.extend_from_slice(&(r.identity.len() as u32).to_le_bytes());
    b.extend_from_slice(r.identity.as_bytes());
    b.extend_from_slice(&(r.kind.len() as u32).to_le_bytes());
    b.extend_from_slice(r.kind.as_bytes());
    b.extend_from_slice(
        &u64::try_from(r.line)
            .map_err(|_| "declaration line overflow")?
            .to_le_bytes(),
    );
    b.extend_from_slice(&(r.sha256.len() as u32).to_le_bytes());
    b.extend_from_slice(r.sha256.as_bytes());
    b.extend_from_slice(&(r.dependencies.len() as u32).to_le_bytes());
    for s in &r.dependencies {
        b.extend_from_slice(&(s.len() as u32).to_le_bytes());
        b.extend_from_slice(s.as_bytes());
    }
    Ok(b)
}
struct Cursor<'a>(&'a [u8]);
impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        if n > self.0.len() {
            return Err("truncated declaration report record".into());
        }
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Ok(a)
    }
    fn u32(&mut self) -> Result<usize> {
        usize::try_from(u32::from_le_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| "truncated declaration report record")?,
        ))
        .map_err(|_| "declaration length overflow".into())
    }
    fn text(&mut self, max: usize) -> Result<String> {
        let n = self.u32()?;
        if n > max {
            return Err("declaration string limit exceeded".into());
        }
        std::str::from_utf8(self.take(n)?)
            .map(str::to_owned)
            .map_err(|_| "invalid declaration report UTF-8".into())
    }
}
fn decode(bytes: &[u8]) -> Result<LeanDeclarationReport> {
    if bytes.is_empty() || bytes.len() > MAX_RECORD {
        return Err("invalid declaration report record length".into());
    }
    let mut c = Cursor(bytes);
    let name = c.text(MAX_PART)?;
    let identity = c.text(MAX_PART)?;
    let kind = c.text(MAX_KIND)?;
    let line = u64::from_le_bytes(
        c.take(8)?
            .try_into()
            .map_err(|_| "truncated declaration line")?,
    );
    let line = usize::try_from(line).map_err(|_| "declaration line overflow")?;
    let sha256 = c.text(MAX_HASH)?;
    let count = c.u32()?;
    if count > super::MAX_DEPENDENCIES {
        return Err("declaration dependency count limit exceeded".into());
    }
    // Every dependency needs a four byte length prefix; enforce that before
    // allocating from an untrusted count.
    if count > c.0.len() / 4
        || count
            .checked_mul(32)
            .is_none_or(|n| n > super::MAX_NAME_BYTES)
    {
        return Err("truncated or oversized declaration dependencies".into());
    }
    let mut dependencies = Vec::with_capacity(count);
    let mut weight = 0usize;
    for _ in 0..count {
        let s = c.text(MAX_PART)?;
        weight = weight
            .checked_add(s.len())
            .and_then(|n| n.checked_add(32))
            .filter(|n| *n <= super::MAX_NAME_BYTES)
            .ok_or("declaration dependency byte limit exceeded")?;
        dependencies.push(s)
    }
    if !c.0.is_empty() {
        return Err("trailing declaration report bytes".into());
    }
    let r = LeanDeclarationReport {
        name,
        identity,
        kind,
        line,
        sha256,
        dependencies,
    };
    validate(&r)?;
    Ok(r)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn report(name: &str, deps: Vec<String>, line: usize) -> LeanDeclarationReport {
        LeanDeclarationReport {
            name: name.into(),
            identity: "pkg.λ.identity".into(),
            kind: "theorem".into(),
            line,
            sha256: "a1".repeat(32),
            dependencies: deps,
        }
    }

    #[test]
    fn codec_preserves_every_field_and_unicode() {
        let original = report("命題.λ", vec!["依存.一".into(), "e\u{301}".into()], 987654);
        assert_eq!(decode(&encode(&original).unwrap()).unwrap(), original);
        assert_eq!(
            encode_len(&original).unwrap(),
            encode(&original).unwrap().len()
        );
    }

    #[test]
    fn codec_rejects_malformed_lengths_counts_utf8_and_trailing_data() {
        let value = report("x", vec![], 1);
        let valid = encode(&value).unwrap();
        assert!(decode(&valid[..valid.len() - 1]).is_err());
        let mut trailing = valid.clone();
        trailing.push(0);
        assert!(decode(&trailing).is_err());
        let mut utf8 = valid.clone();
        utf8[4] = 0xff;
        assert!(decode(&utf8).is_err());
        let mut name_len = valid.clone();
        name_len[..4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(decode(&name_len).is_err());
        let mut dep_count = valid.clone();
        let at = dep_count.len() - 4;
        dep_count[at..].copy_from_slice(&(super::super::MAX_DEPENDENCIES as u32).to_le_bytes());
        assert!(decode(&dep_count).is_err());
        let mut excessive = valid;
        let at = excessive.len() - 4;
        excessive[at..]
            .copy_from_slice(&((super::super::MAX_DEPENDENCIES + 1) as u32).to_le_bytes());
        assert!(decode(&excessive).is_err());
    }

    #[test]
    fn inventory_spills_large_cross_page_records_and_preserves_order() {
        // Each string stays within the name limit, while each record crosses
        // a page and the complete inventory exceeds the resident page cache.
        let deps = vec!["λ".repeat(7_000); 6];
        let values = (0..12)
            .map(|id| report(&format!("report{id}"), deps.clone(), id + 4))
            .collect::<Vec<_>>();
        let mut store = Inventory::with_limit(0);
        for value in &values {
            store.push(value.clone()).unwrap();
        }
        assert!(store.is_spilled());
        for id in [0, 10, 1, 11, 4] {
            assert_eq!(&*store.get(id).unwrap(), &values[id]);
        }
        assert!(store.get(values.len()).is_err());
        assert_eq!(store.into_vec().unwrap(), values);
    }

    #[test]
    fn selected_scratch_capacity_rejects_first_spilled_record() {
        let mut store = Inventory::build(0, super::super::MAX_DECLARATIONS, 8);
        assert!(store.push(report("small", vec![], 1)).is_err());
        assert!(store.is_spilled());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn threshold_counts_vector_capacity_and_owned_string_capacity() {
        let value = report("small", vec!["dependency".into()], 1);
        let mut resident = Inventory::with_limit(1024 * 1024);
        resident.push(value.clone()).unwrap();
        assert!(!resident.is_spilled());
        let one = memory_weight(&value).unwrap() + std::mem::size_of::<LeanDeclarationReport>();
        let mut bounded = Inventory::with_limit(one);
        bounded.push(value.clone()).unwrap();
        assert!(
            bounded.is_spilled(),
            "the first Vec allocation holds four rows"
        );
        let mut reserved = value;
        reserved.name = String::with_capacity(8192);
        reserved.name.push_str("small");
        let mut bounded = Inventory::with_limit(4096);
        bounded.push(reserved).unwrap();
        assert!(bounded.is_spilled());
        assert_eq!(bounded.into_vec().unwrap().len(), 1);
    }

    #[test]
    fn malformed_spool_indexes_fail_closed() {
        let mut spilled = Spilled {
            index: RefCell::new(Spool::new().unwrap()),
            data: RefCell::new(Spool::new().unwrap()),
            count: 1,
        };
        spilled.data.get_mut().append(&[0; 12]).unwrap();
        let mut index = [0u8; INDEX_BYTES];
        index[..8].copy_from_slice(&0u64.to_le_bytes());
        index[8..].copy_from_slice(&u64::MAX.to_le_bytes());
        spilled.index.get_mut().append(&index).unwrap();
        assert!(spilled.get(0).is_err());
        assert!(spilled.matches_identity(0, "key").is_err());
        let missing = Spilled {
            index: RefCell::new(Spool::new().unwrap()),
            data: RefCell::new(Spool::new().unwrap()),
            count: 1,
        };
        assert!(missing.get(0).is_err());
        assert!(missing.matches_identity(0, "key").is_err());
    }

    #[test]
    fn identity_lookup_preserves_keys_across_page_and_chunk_boundaries() {
        let mut filler = report("padding", vec!["p".repeat(MAX_PART); 3], 1);
        let fill = PAGE - 2 - encode(&filler).unwrap().len() - 4;
        assert!(fill <= MAX_PART);
        filler.dependencies.push("p".repeat(fill));
        assert_eq!(encode(&filler).unwrap().len(), PAGE - 2);
        let mut value = report("a different display name", vec![], 2);
        value.identity = "λ".repeat(MAX_PART / 2);
        for limit in [0, usize::MAX] {
            let mut inventory = Inventory::with_limit(limit);
            inventory.push(filler.clone()).unwrap();
            inventory.push(value.clone()).unwrap();
            assert!(inventory.matches_identity(1, &value.identity).unwrap());
            assert!(!inventory.matches_identity(1, &value.name).unwrap());
            assert!(!inventory.matches_identity(1, "").unwrap());
            let mut different = value.identity.clone();
            different.truncate(different.len() - 2);
            different.push('μ');
            assert!(!inventory.matches_identity(1, &different).unwrap());
            assert!(inventory.matches_identity(2, &value.identity).is_err());
        }
    }

    #[test]
    fn identity_lookup_cannot_read_fields_past_the_record_boundary() {
        let valid = encode(&report("display", vec![], 1)).unwrap();
        let identity_length_at = 4 + "display".len();
        let cases = [
            (valid.clone(), 3),
            (valid.clone(), identity_length_at + 3),
            (valid.clone(), identity_length_at + 4),
            (
                {
                    let mut bytes = valid.clone();
                    bytes[..4].copy_from_slice(&u32::MAX.to_le_bytes());
                    bytes
                },
                valid.len(),
            ),
            (
                {
                    let mut bytes = valid.clone();
                    bytes[identity_length_at..identity_length_at + 4]
                        .copy_from_slice(&u32::MAX.to_le_bytes());
                    bytes
                },
                valid.len(),
            ),
        ];
        for (bytes, len) in cases {
            let mut store = Spilled {
                index: RefCell::new(Spool::new().unwrap()),
                data: RefCell::new(Spool::new().unwrap()),
                count: 1,
            };
            store.data.get_mut().append(&bytes).unwrap();
            let mut index = [0; INDEX_BYTES];
            index[8..].copy_from_slice(&(len as u64).to_le_bytes());
            store.index.get_mut().append(&index).unwrap();
            assert!(store.matches_identity(0, "pkg.λ.identity").is_err());
        }
    }

    #[test]
    fn name_identity_matches_for_memory_and_spilled_unicode_records() {
        let mut value = report(&"界".repeat(MAX_PART / 3), vec![], 1);
        value.identity = "λ🧭".repeat(MAX_PART / 6);
        let mut filler = report("pad", vec!["x".repeat(MAX_PART); 3], 2);
        filler.dependencies.push("x".repeat(MAX_PART / 2));
        for limit in [usize::MAX, 0] {
            let mut inventory = Inventory::with_limit(limit);
            inventory.push(filler.clone()).unwrap();
            inventory.push(value.clone()).unwrap();
            assert_eq!(
                inventory.name_identity(1).unwrap(),
                (value.name.clone(), value.identity.clone())
            );
            assert!(inventory.name_identity(2).is_err());
        }
    }

    #[test]
    fn name_identity_rejects_bad_lengths_utf8_and_protected_corruption() {
        let valid = encode(&report("display", vec![], 1)).unwrap();
        let identity_at = 4 + "display".len();
        for (bytes, len) in [
            (
                {
                    let mut b = valid.clone();
                    b[..4].copy_from_slice(&u32::MAX.to_le_bytes());
                    b
                },
                valid.len(),
            ),
            (
                {
                    let mut b = valid.clone();
                    b[identity_at..identity_at + 4].copy_from_slice(&u32::MAX.to_le_bytes());
                    b
                },
                valid.len(),
            ),
            (
                {
                    let mut b = valid.clone();
                    b[4] = 0xff;
                    b
                },
                valid.len(),
            ),
            (valid.clone(), 3),
        ] {
            let mut store = Spilled {
                index: RefCell::new(Spool::new().unwrap()),
                data: RefCell::new(Spool::new().unwrap()),
                count: 1,
            };
            store.data.get_mut().append(&bytes).unwrap();
            let mut index = [0; INDEX_BYTES];
            index[8..].copy_from_slice(&(len as u64).to_le_bytes());
            store.index.get_mut().append(&index).unwrap();
            assert!(store.name_identity(0).is_err());
        }

        let mut store = Spilled {
            index: RefCell::new(Spool::new().unwrap()),
            data: RefCell::new(Spool::new().unwrap()),
            count: 1,
        };
        let mut bytes = encode(&report("protected", vec![], 1)).unwrap();
        bytes.resize(PAGE + 1, 0);
        store.data.get_mut().append(&bytes).unwrap();
        let mut index = [0; INDEX_BYTES];
        index[8..].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
        store.index.get_mut().append(&index).unwrap();
        store.data.get_mut().clear_cache();
        store.data.get_mut().overwrite_flushed(4, &[b'X']).unwrap();
        assert!(store.name_identity(0).is_err());
    }

    #[test]
    fn selected_count_limit_caps_push_without_preallocating() {
        let mut store = Inventory::with_count_limit(1);
        store.push(report("one", vec![], 1)).unwrap();
        assert!(store
            .push(report("two", vec![], 2))
            .unwrap_err()
            .contains("count limit"));
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn selected_count_limit_can_exceed_default_declaration_cap() {
        let max_count = super::super::MAX_DECLARATIONS + 1;
        let mut store = Inventory::with_count_limit(max_count);
        for line in 0..max_count {
            store
                .push(report(&format!("name{line}"), vec![], line + 1))
                .unwrap();
        }
        assert_eq!(store.len(), max_count);
    }
}
