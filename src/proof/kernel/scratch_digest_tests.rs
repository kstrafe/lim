use super::{Digests, Spool};

const PAGE: usize = 64 * 1024;
const DIGEST_LIMIT: usize = 1024;

fn identity(index: usize) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[..8].copy_from_slice(&(index as u64).to_le_bytes());
    bytes[8..16].copy_from_slice(&(!(index as u64)).to_le_bytes());
    bytes[16..].copy_from_slice(&[0x5a; 16]);
    bytes
}

#[test]
fn digest_rows_preserve_identity_in_order_across_spill_and_page_boundaries() {
    let mut digests = Digests::new();
    let rows = DIGEST_LIMIT + 37;
    for index in 0..rows {
        digests.push(identity(index)).unwrap();
    }

    assert_eq!(digests.len(), rows);
    assert!(digests.is_spilled());
    // Include the child spool's pending page and bounded read cache.
    assert!(digests.resident_bytes() < 512 * 1024);
    for index in [
        0,
        1,
        DIGEST_LIMIT - 1,
        DIGEST_LIMIT,
        DIGEST_LIMIT + 1,
        rows - 1,
    ] {
        assert_eq!(digests.get(index).unwrap(), identity(index));
    }
    digests.healthy().unwrap();
}

#[test]
fn digest_corruption_poisoning_is_sticky_after_cache_hits_and_appends() {
    let mut digests = Digests::new();
    for index in 0..DIGEST_LIMIT + 8 {
        digests.push(identity(index)).unwrap();
    }
    assert!(digests.is_spilled());

    // Warm a row before corruption; a cached digest must not restore trust.
    assert_eq!(digests.get(3).unwrap(), identity(3));
    digests.corrupt_flushed().unwrap();
    assert!(digests.get(3).is_err());
    assert!(digests.healthy().is_err());
    assert!(digests.push(identity(DIGEST_LIMIT + 8)).is_err());
    assert!(digests.get(DIGEST_LIMIT - 1).is_err());
}

#[test]
fn parent_page_spool_streams_many_pages_and_detects_digest_storage_corruption() {
    let mut spool = Spool::new().unwrap();
    let mut buffer = vec![0; PAGE];
    let pages = DIGEST_LIMIT + 1;
    for page in 0..pages {
        for (offset, byte) in buffer.iter_mut().enumerate() {
            *byte = ((page.wrapping_mul(31) + offset.wrapping_mul(17)) % 251) as u8;
        }
        spool.append(&buffer).unwrap();
    }
    assert_eq!(spool.len(), (pages * PAGE) as u64);
    assert!(spool.digests_spilled());

    let mut readback = vec![0; PAGE];
    for page in [0, pages / 2, pages - 1] {
        spool
            .read_into((page * PAGE) as u64, &mut readback)
            .unwrap();
        for (offset, byte) in readback.iter().enumerate() {
            assert_eq!(
                *byte,
                ((page.wrapping_mul(31) + offset.wrapping_mul(17)) % 251) as u8
            );
        }
    }

    spool.corrupt_digests().unwrap();
    // Page 1 is cold; previously read data pages can still hold valid bytes
    // until an integrity failure is actually observed.
    assert!(spool.read_into(PAGE as u64, &mut readback).is_err());
    // Reading a cached page and appending still fail after the digest failure.
    assert!(spool
        .read_into(((pages - 1) * PAGE) as u64, &mut readback)
        .is_err());
    assert!(spool.append(&[7]).is_err());
}

#[test]
fn metadata_only_digest_storage_handles_ten_thousand_rows() {
    let mut digests = Digests::new();
    for index in 0..10_000 {
        digests.push(identity(index)).unwrap();
    }
    assert_eq!(digests.len(), 10_000);
    assert!(digests.is_spilled());
    for index in [0, 511, 1023, 1024, 4095, 8191, 9999] {
        assert_eq!(digests.get(index).unwrap(), identity(index));
    }
    digests.healthy().unwrap();
}

#[test]
#[cfg(target_pointer_width = "64")]
fn selected_digest_backing_reads_and_authenticates_past_128_mib() {
    const PAGE: usize = 64 * 1024;
    const DIGEST_BYTES: usize = 32;
    const OLD_EDGE: usize = 128 * 1024 * 1024;
    let mut digests = Digests::with_data_limit(300 * 1024 * 1024 * 1024).unwrap();
    let rows = OLD_EDGE / DIGEST_BYTES + PAGE / DIGEST_BYTES + 1;
    for index in 0..rows {
        digests.push(identity(index)).unwrap();
    }

    assert!(digests.is_spilled());
    assert!(digests.resident_bytes() < 2 * 1024 * 1024);
    let edge_index = OLD_EDGE / DIGEST_BYTES;
    digests.clear_cache();
    for index in [edge_index - 1, edge_index, edge_index + 1] {
        assert_eq!(digests.get(index).unwrap(), identity(index));
        assert!(digests.resident_bytes() < 2 * 1024 * 1024);
    }

    // Corrupt a flushed metadata record beyond the old backing ceiling. The
    // child's cold-page checksum failure must poison this parent digest store.
    digests.corrupt_flushed_at(OLD_EDGE as u64).unwrap();
    assert!(digests.get(edge_index).is_err());
    assert!(digests.healthy().is_err());
    assert!(digests.get(edge_index - 1).is_err());
}

#[test]
fn failed_digest_publication_after_data_write_invalidates_the_parent() {
    let mut spool = Spool::new().unwrap();
    let page = vec![19; PAGE];
    for _ in 0..DIGEST_LIMIT + 1 {
        spool.append(&page).unwrap();
    }
    let committed = spool.len();
    spool.exhaust_digest_backing().unwrap();
    assert!(spool.append(&page).unwrap_err().contains("byte limit"));
    assert_eq!(spool.len(), committed);
    assert!(spool
        .read_into(committed - PAGE as u64, &mut [0; 1])
        .is_err());
    assert!(spool.read_into(committed, &mut []).is_err());
    assert!(spool.append(&[1]).is_err());
}

#[test]
#[ignore = "manual metadata-only storage benchmark; not proof or FLT coverage"]
fn million_digest_metadata_benchmark() {
    use std::{hint::black_box, time::Instant};
    const ROWS: usize = 1_052_234;
    let mode = std::env::var("LIM_DIGEST_BENCH_MODE").expect("select vec or paged");
    assert!(matches!(mode.as_str(), "vec" | "paged"));
    let started = Instant::now();
    let resident;
    if mode == "vec" {
        let mut rows = Vec::new();
        for index in 0..ROWS {
            rows.push(identity(index));
        }
        for index in [0, 1023, 1024, ROWS / 2, ROWS - 1] {
            assert_eq!(rows[index], identity(index));
        }
        resident = rows.capacity() * 32;
        black_box(&rows);
    } else {
        let mut rows = Digests::new();
        for index in 0..ROWS {
            rows.push(identity(index)).unwrap();
        }
        for index in [0, 1023, 1024, ROWS / 2, ROWS - 1] {
            assert_eq!(rows.get(index).unwrap(), identity(index));
        }
        resident = rows.resident_bytes();
        assert!(resident < 512 * 1024);
        black_box(&rows);
    }
    println!("lim-digest-benchmark {{\"mode\":\"{mode}\",\"rows\":{ROWS},\"resident_bytes\":{resident},\"wall_ns\":{}}}", started.elapsed().as_nanos());
}
