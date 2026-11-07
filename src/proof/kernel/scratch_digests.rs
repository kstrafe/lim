//! Bounded, invocation-local storage for scratch page digests.
use super::{Result, Spool};

const RESIDENT_ENTRIES: usize = 1024;
const DIGEST_BYTES: usize = 32;
const DEFAULT_BACKING_BYTES: u64 = 128 * 1024 * 1024;

pub(super) struct Digests {
    storage: Storage,
    count: usize,
    poisoned: bool,
    backing_limit: u64,
}

enum Storage {
    Resident(Vec<[u8; DIGEST_BYTES]>),
    Spilled(Box<Spool>),
}

impl Digests {
    pub(super) fn new() -> Self {
        Self {
            storage: Storage::Resident(Vec::new()),
            count: 0,
            poisoned: false,
            backing_limit: DEFAULT_BACKING_BYTES,
        }
    }

    pub(super) fn with_data_limit(data_limit: u64) -> Result<Self> {
        let page_size = 64 * 1024;
        let pages = data_limit / page_size + u64::from(data_limit % page_size != 0);
        let required = pages
            .checked_mul(DIGEST_BYTES as u64)
            .ok_or("replay scratch digest backing limit overflow")?;
        if required <= DEFAULT_BACKING_BYTES {
            Ok(Self::new())
        } else {
            Ok(Self {
                storage: Storage::Resident(Vec::new()),
                count: 0,
                poisoned: false,
                backing_limit: required,
            })
        }
    }

    pub(super) fn len(&self) -> usize {
        self.count
    }

    pub(super) fn healthy(&self) -> Result<()> {
        if self.poisoned {
            Err("replay scratch digests are invalid after a storage error".into())
        } else if let Storage::Spilled(spool) = &self.storage {
            if let Err(error) = spool.healthy() {
                Err(error)
            } else {
                Ok(())
            }
        } else {
            Ok(())
        }
    }

    pub(super) fn push(&mut self, digest: [u8; DIGEST_BYTES]) -> Result<()> {
        self.healthy()?;
        let next_count = self
            .count
            .checked_add(1)
            .ok_or("replay scratch digest count overflow")?;
        if let Storage::Resident(resident) = &mut self.storage {
            if resident.len() < RESIDENT_ENTRIES {
                if resident.len() == resident.capacity() {
                    let additional = resident
                        .capacity()
                        .max(4)
                        .min(RESIDENT_ENTRIES - resident.len());
                    if let Err(error) = resident.try_reserve_exact(additional) {
                        self.poisoned = true;
                        return Err(format!("cannot retain scratch page digests: {error}"));
                    }
                }
                resident.push(digest);
                self.count = next_count;
                return Ok(());
            }
        }

        if matches!(self.storage, Storage::Resident(_)) {
            if let Err(error) = self.spill_resident() {
                self.poisoned = true;
                return Err(error);
            }
        }
        let result = match &mut self.storage {
            Storage::Spilled(spool) => spool.append(&digest).map(|_| ()),
            Storage::Resident(_) => unreachable!(),
        };
        if let Err(error) = result {
            self.poisoned = true;
            return Err(error);
        }
        self.count = next_count;
        Ok(())
    }

    pub(super) fn get(&mut self, index: usize) -> Result<[u8; DIGEST_BYTES]> {
        self.healthy()?;
        if index >= self.count {
            return Err("replay scratch digest index is out of range".into());
        }
        match &mut self.storage {
            Storage::Resident(resident) => Ok(resident[index]),
            Storage::Spilled(spool) => {
                let offset = index
                    .checked_mul(DIGEST_BYTES)
                    .ok_or("replay scratch digest offset overflow")?;
                let offset =
                    u64::try_from(offset).map_err(|_| "replay scratch digest offset overflow")?;
                let mut digest = [0; DIGEST_BYTES];
                if let Err(error) = spool.read_into(offset, &mut digest) {
                    self.poisoned = true;
                    return Err(error);
                }
                Ok(digest)
            }
        }
    }

    fn spill_resident(&mut self) -> Result<()> {
        let Storage::Resident(resident) = &self.storage else {
            return Ok(());
        };
        let mut spool = Spool::with_limit(self.backing_limit)?;
        let mut bytes = Vec::with_capacity(RESIDENT_ENTRIES * DIGEST_BYTES);
        for digest in resident {
            bytes.extend_from_slice(digest);
        }
        spool.append(&bytes)?;

        // Verify every resident record before releasing the only in-memory copy.
        let mut restored = vec![0; bytes.len()];
        for (offset, chunk) in restored.chunks_mut(64 * 1024).enumerate() {
            spool.read_into((offset * 64 * 1024) as u64, chunk)?;
        }
        if restored != bytes {
            return Err("replay scratch digest spill round-trip mismatch".into());
        }
        self.storage = Storage::Spilled(Box::new(spool));
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn resident_bytes(&self) -> usize {
        match &self.storage {
            Storage::Resident(values) => values.capacity() * DIGEST_BYTES,
            Storage::Spilled(spool) => std::mem::size_of::<Spool>() + 64 + spool.resident_bytes(),
        }
    }

    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.storage, Storage::Spilled(_))
    }

    #[cfg(test)]
    pub(super) fn corrupt_flushed(&mut self) -> Result<()> {
        let Storage::Spilled(spool) = &mut self.storage else {
            return Err("replay scratch digests are not spilled".into());
        };
        if let Err(error) = spool.append(&vec![0; 64 * 1024]) {
            self.poisoned = true;
            return Err(error);
        }
        if let Err(error) = spool.overwrite_flushed(0, b"!") {
            self.poisoned = true;
            return Err(error);
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn clear_cache(&mut self) {
        if let Storage::Spilled(spool) = &mut self.storage {
            spool.clear_cache();
        }
    }

    #[cfg(test)]
    pub(super) fn corrupt_flushed_at(&mut self, offset: u64) -> Result<()> {
        let Storage::Spilled(spool) = &mut self.storage else {
            return Err("replay scratch digests are not spilled".into());
        };
        if let Err(error) = spool.overwrite_flushed(offset, b"!") {
            self.poisoned = true;
            return Err(error);
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn exhaust_backing(&mut self) -> Result<()> {
        let Storage::Spilled(spool) = &mut self.storage else {
            return Err("replay scratch digests are not spilled".into());
        };
        // A healthy child refuses its next append at the normal byte ceiling.
        // This lets the parent test fail after writing its own data page.
        spool.len = spool.limit;
        Ok(())
    }
}
