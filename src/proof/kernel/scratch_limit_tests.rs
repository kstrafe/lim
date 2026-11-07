use super::*;

#[test]
fn selected_limit_is_validated_before_spool_creation() {
    assert!(Spool::with_limit(0).is_err());
    assert!(Spool::with_limit(MAX_SELECTED_BYTES + 1).is_err());
    assert!(Spool::with_limit(u64::MAX).is_err());
    assert_eq!(Spool::with_limit(1).unwrap().limit, 1);
    assert_eq!(
        Spool::with_limit(MAX_SELECTED_BYTES).unwrap().limit,
        MAX_SELECTED_BYTES
    );
}

#[test]
#[cfg(target_pointer_width = "64")]
fn constructor_above_256_gib_has_small_metadata_residency() {
    let spool = Spool::with_limit(300 * 1024 * 1024 * 1024).unwrap();
    assert_eq!(spool.len(), 0);
    assert_eq!(spool.limit, 300 * 1024 * 1024 * 1024);
    assert!(spool.resident_bytes() < 1024 * 1024);
}

#[test]
fn selected_small_limit_has_exact_append_boundary() {
    let mut spool = Spool::with_limit(PAGE as u64 + 3).unwrap();
    spool.append(&vec![0x5a; PAGE + 3]).unwrap();
    assert_eq!(spool.len(), (PAGE + 3) as u64);
    assert!(spool.append(&[1]).unwrap_err().contains("byte limit"));
    assert_eq!(spool.len(), (PAGE + 3) as u64);
    assert_eq!(spool.read(PAGE as u64 - 2, 5).unwrap(), [0x5a; 5]);
}

#[test]
fn large_selected_spool_streams_cold_pages_with_bounded_residency() {
    let total = 128 * 1024 * 1024 + PAGE * 3 + 17;
    let mut spool = Spool::with_limit(total as u64).unwrap();
    let mut page_bytes = vec![0; PAGE];
    let full_pages = total / PAGE;
    for page_index in 0..full_pages {
        for (within, byte) in page_bytes.iter_mut().enumerate() {
            *byte = page_pattern(page_index, within);
        }
        spool.append(&page_bytes).unwrap();
    }
    let tail_len = total % PAGE;
    for (within, byte) in page_bytes[..tail_len].iter_mut().enumerate() {
        *byte = page_pattern(full_pages, within);
    }
    spool.append(&page_bytes[..tail_len]).unwrap();
    assert_eq!(spool.len(), total as u64);
    assert!(spool.digests_spilled());

    spool.clear_cache();
    for index in [0, 128 * 1024 * 1024 / PAGE, full_pages - 1] {
        spool
            .read_into((index * PAGE) as u64, &mut page_bytes)
            .unwrap();
        assert!(page_bytes
            .iter()
            .enumerate()
            .all(|(within, byte)| *byte == page_pattern(index, within)));
        assert!(spool.cache.len() <= CACHE_PAGES);
        assert!(spool.resident_bytes() < 2 * 1024 * 1024);
    }

    // A cold read spanning the former 128 MiB ceiling must return bytes from
    // both independently patterned pages on either side of the boundary.
    let boundary = 128 * 1024 * 1024;
    let mut crossing = [0; 64];
    spool
        .read_into((boundary - 32) as u64, &mut crossing)
        .unwrap();
    for (index, byte) in crossing.iter().enumerate() {
        let absolute = boundary - 32 + index;
        assert_eq!(
            *byte,
            page_pattern(absolute / PAGE, absolute % PAGE),
            "mismatched byte at absolute offset {absolute}"
        );
    }
    assert!(spool.resident_bytes() < 2 * 1024 * 1024);

    // Tampering with an evicted, flushed page beyond the former ceiling must
    // poison the spool and block later reads.
    spool.overwrite_flushed(boundary as u64, &[0xff]).unwrap();
    assert!(spool
        .read_into(boundary as u64, &mut crossing)
        .unwrap_err()
        .contains("checksum"));
    assert!(spool
        .read_into(boundary as u64, &mut crossing)
        .unwrap_err()
        .contains("invalid after"));
    assert!(spool.append(&[0]).unwrap_err().contains("invalid after"));
}

fn page_pattern(page_index: usize, within: usize) -> u8 {
    if within < std::mem::size_of::<usize>() {
        (page_index >> (within * 8)) as u8
    } else {
        ((page_index.wrapping_mul(31) + within.wrapping_mul(17)) % 251) as u8
    }
}
