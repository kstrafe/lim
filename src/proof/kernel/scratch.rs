//! Append-only invocation-local scratch bytes with bounded resident pages.
//! The current process protects page digests; no pathname or prior process's
//! storage is accepted as a source of checked evidence.
use super::{hash::Sha256, Result};
use std::{
    collections::VecDeque,
    fs::{File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    sync::atomic::{AtomicU64, Ordering},
};

const PAGE: usize = 64 * 1024;
const CACHE_PAGES: usize = 4;
pub(in crate::proof::kernel) const DEFAULT_BYTES: u64 = 128 * 1024 * 1024;
pub(in crate::proof::kernel) const MAX_SELECTED_BYTES: u64 = isize::MAX as u64;
static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

#[path = "scratch_digests.rs"]
mod digests;
use digests::Digests;

struct CachedPage {
    index: usize,
    bytes: Vec<u8>,
}

pub(in crate::proof::kernel) struct Spool {
    file: File,
    pending: Vec<u8>,
    digests: Digests,
    cache: VecDeque<CachedPage>,
    len: u64,
    limit: u64,
    poisoned: bool,
}

impl Spool {
    pub(in crate::proof::kernel) fn new() -> Result<Self> {
        Self::with_limit(DEFAULT_BYTES)
    }

    pub(in crate::proof::kernel) fn with_limit(limit: u64) -> Result<Self> {
        let pages = limit / PAGE as u64 + u64::from(limit % PAGE as u64 != 0);
        if limit == 0 || limit > MAX_SELECTED_BYTES || usize::try_from(pages).is_err() {
            return Err("replay scratch byte limit is invalid".into());
        }
        let digests = Digests::with_data_limit(limit)?;
        let mut options = OpenOptions::new();
        options.read(true).write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        for _ in 0..32 {
            let nonce = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!(".lim-replay-{}-{nonce}", std::process::id()));
            match options.open(&path) {
                Ok(file) => {
                    // An open unlinked file has no reusable cache pathname.
                    // Closing it reclaims its storage, including on an error.
                    std::fs::remove_file(&path).map_err(io_error)?;
                    return Ok(Self {
                        file,
                        pending: Vec::with_capacity(PAGE),
                        digests,
                        cache: VecDeque::new(),
                        len: 0,
                        limit,
                        poisoned: false,
                    });
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(io_error(error)),
            }
        }
        Err("replay scratch file creation collision limit exceeded".into())
    }

    pub(in crate::proof::kernel) fn len(&self) -> u64 {
        self.len
    }

    #[cfg(test)]
    pub(in crate::proof::kernel) fn resident_bytes(&self) -> usize {
        self.pending.capacity()
            + self.digests.resident_bytes()
            + self.cache.capacity() * std::mem::size_of::<CachedPage>()
            + self
                .cache
                .iter()
                .map(|page| page.bytes.capacity())
                .sum::<usize>()
    }

    #[cfg(test)]
    pub(in crate::proof::kernel) fn clear_cache(&mut self) {
        self.cache.clear();
    }

    #[cfg(test)]
    fn digests_spilled(&self) -> bool {
        self.digests.is_spilled()
    }

    #[cfg(test)]
    fn corrupt_digests(&mut self) -> Result<()> {
        self.digests.corrupt_flushed()
    }

    #[cfg(test)]
    fn exhaust_digest_backing(&mut self) -> Result<()> {
        self.digests.exhaust_backing()
    }

    #[cfg(test)]
    pub(in crate::proof::kernel) fn overwrite_flushed(
        &mut self,
        offset: u64,
        bytes: &[u8],
    ) -> Result<()> {
        if offset
            .checked_add(bytes.len() as u64)
            .is_none_or(|end| end > self.digests.len() as u64 * PAGE as u64)
        {
            return Err("test write must stay inside flushed scratch pages".into());
        }
        self.file.seek(SeekFrom::Start(offset)).map_err(io_error)?;
        self.file.write_all(bytes).map_err(io_error)?;
        self.clear_cache();
        Ok(())
    }

    pub(in crate::proof::kernel) fn append(&mut self, mut bytes: &[u8]) -> Result<u64> {
        self.healthy()?;
        let end = self
            .len
            .checked_add(u64::try_from(bytes.len()).map_err(|_| "replay scratch length overflow")?)
            .filter(|end| *end <= self.limit)
            .ok_or("replay scratch byte limit exceeded")?;
        let start = self.len;
        while !bytes.is_empty() {
            let count = (PAGE - self.pending.len()).min(bytes.len());
            self.pending.extend_from_slice(&bytes[..count]);
            bytes = &bytes[count..];
            if self.pending.len() == PAGE {
                let result = (|| {
                    self.file
                        .seek(SeekFrom::Start(self.digests.len() as u64 * PAGE as u64))?;
                    self.file.write_all(&self.pending)
                })();
                if let Err(error) = result {
                    self.poisoned = true;
                    return Err(io_error(error));
                }
                let index = self.digests.len();
                if let Err(error) = self.digests.push(digest(&self.pending)) {
                    // Data may already be written, but its authenticated index
                    // was not published. No later cache hit may hide the error.
                    self.poisoned = true;
                    return Err(error);
                }
                let bytes = std::mem::replace(&mut self.pending, Vec::with_capacity(PAGE));
                if self.cache.len() == CACHE_PAGES {
                    self.cache.pop_front();
                }
                self.cache.push_back(CachedPage { index, bytes });
            }
        }
        self.len = end;
        Ok(start)
    }

    #[cfg(test)]
    fn read(&mut self, offset: u64, len: usize) -> Result<Vec<u8>> {
        let mut bytes = vec![0; len];
        self.read_into(offset, &mut bytes)?;
        Ok(bytes)
    }
    pub(in crate::proof::kernel) fn read_into(
        &mut self,
        offset: u64,
        result: &mut [u8],
    ) -> Result<()> {
        self.healthy()?;
        let len = result.len();
        if len > PAGE
            || offset
                .checked_add(len as u64)
                .is_none_or(|end| end > self.len)
        {
            return Err("replay scratch read range is invalid".into());
        }
        let mut used = 0;
        let mut cursor = offset;
        while used < len {
            let page = usize::try_from(cursor / PAGE as u64)
                .map_err(|_| "replay scratch offset overflow")?;
            let within = (cursor % PAGE as u64) as usize;
            let count = (PAGE - within).min(len - used);
            let bytes = if page == self.digests.len() {
                &self.pending
            } else {
                self.load(page)?;
                &self
                    .cache
                    .back()
                    .ok_or("missing replay scratch page")?
                    .bytes
            };
            result[used..used + count].copy_from_slice(&bytes[within..within + count]);
            used += count;
            cursor += count as u64;
        }
        Ok(())
    }

    fn load(&mut self, index: usize) -> Result<()> {
        if let Some(at) = self.cache.iter().position(|page| page.index == index) {
            let page = self.cache.remove(at).ok_or("missing replay scratch page")?;
            self.cache.push_back(page);
            return Ok(());
        }
        let expected = match self.digests.get(index) {
            Ok(expected) => expected,
            Err(error) => {
                self.poisoned = true;
                return Err(error);
            }
        };
        let mut bytes = vec![0; PAGE];
        let result = (|| {
            self.file
                .seek(SeekFrom::Start(index as u64 * PAGE as u64))?;
            self.file.read_exact(&mut bytes)
        })();
        if let Err(error) = result {
            self.poisoned = true;
            return Err(io_error(error));
        }
        if digest(&bytes) != expected {
            self.poisoned = true;
            return Err("replay scratch page checksum mismatch".into());
        }
        if self.cache.len() == CACHE_PAGES {
            self.cache.pop_front();
        }
        self.cache.push_back(CachedPage { index, bytes });
        Ok(())
    }

    fn healthy(&self) -> Result<()> {
        if self.poisoned {
            Err("replay scratch storage is invalid after an I/O or checksum error".into())
        } else {
            self.digests.healthy()
        }
    }
}

fn digest(bytes: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(bytes);
    hash.finish()
}
fn io_error(error: std::io::Error) -> String {
    format!("replay scratch I/O failed: {error}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pending_and_cross_page_reads_match_original_bytes_with_bounded_cache() {
        let mut spool = Spool::new().unwrap();
        let data = (0..PAGE * 7 + 19)
            .map(|i| (i % 251) as u8)
            .collect::<Vec<_>>();
        for chunk in data.chunks(137) {
            spool.append(chunk).unwrap();
        }
        assert_eq!(spool.len(), data.len() as u64);
        for offset in [0, PAGE - 17, PAGE * 5 - 11, PAGE * 7, 23, PAGE * 6] {
            let len = 19.min(data.len() - offset);
            assert_eq!(
                spool.read(offset as u64, len).unwrap(),
                data[offset..offset + len]
            );
            assert!(spool.cache.len() <= CACHE_PAGES);
        }
        assert!(spool.read(data.len() as u64, 1).is_err());
        assert!(spool.read(u64::MAX, 2).is_err());
        assert!(spool.read(0, PAGE + 1).is_err());
    }

    #[test]
    fn corruption_and_truncation_fail_closed_and_poison_later_reads() {
        for truncate in [false, true] {
            let mut spool = Spool::new().unwrap();
            spool.append(&vec![7; PAGE]).unwrap();
            if truncate {
                spool.file.set_len(0).unwrap();
            } else {
                spool.file.seek(SeekFrom::Start(13)).unwrap();
                spool.file.write_all(&[8]).unwrap();
            }
            spool.cache.clear();
            let error = spool.read(0, 32).unwrap_err();
            assert!(
                error.contains(if truncate { "I/O" } else { "checksum" }),
                "{error}"
            );
            assert!(spool.read(0, 1).unwrap_err().contains("invalid after"));
            assert!(spool.append(&[0]).unwrap_err().contains("invalid after"));
        }
    }

    #[test]
    fn byte_limit_refuses_before_any_append() {
        let mut spool = Spool::new().unwrap();
        spool.len = DEFAULT_BYTES;
        assert!(spool.append(&[0]).unwrap_err().contains("byte limit"));
        assert_eq!(spool.len, DEFAULT_BYTES);
        assert!(spool.pending.is_empty());
        assert_eq!(spool.digests.len(), 0);
    }
}

#[cfg(test)]
#[path = "scratch_digest_tests.rs"]
mod digest_tests;

#[cfg(test)]
#[path = "scratch_limit_tests.rs"]
mod limit_tests;
