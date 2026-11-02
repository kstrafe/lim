use super::*;

fn name(index: usize) -> Name {
    Name {
        key: format!("$lean:s5:Probe{}:𝄞\0{index}", "x".repeat(171)),
        display: format!("Probe.\"é\\u0000{index}\"{}", "y".repeat(137)),
        depth: 2,
    }
}

#[test]
fn paged_names_preserve_fields_ids_and_backward_reads_across_page_boundaries() {
    let mut eager = Names::with_limit(usize::MAX);
    let mut paged = Names::with_limit(1024);
    for id in 0..900 {
        let value = name(id);
        eager.push(value.clone()).unwrap();
        paged.push(value).unwrap();
    }
    assert!(!eager.is_spilled());
    assert!(paged.is_spilled());
    assert_eq!(eager.len(), paged.len());
    for id in (0..paged.len()).rev().chain(0..paged.len()) {
        assert_eq!(eager.get(id).unwrap(), paged.get(id).unwrap());
    }
    for id in [0, 1, 42, 315, 899] {
        let original = eager.get(id).unwrap();
        assert_eq!(paged.by_key(&original.key).unwrap().unwrap(), original);
    }
    assert!(paged.by_key("missing").unwrap().is_none());
    assert!(paged
        .get(paged.len())
        .unwrap_err()
        .contains("earlier record"));
    assert!(paged.get(usize::MAX).is_err());
}

#[test]
fn zero_limit_migrates_the_anonymous_root_and_duplicate_keys_still_reject() {
    for limit in [0, usize::MAX] {
        let mut names = Names::with_limit(limit);
        names.push(name(1)).unwrap();
        assert_eq!(names.len(), 2);
        assert_eq!(names.get(0).unwrap().key, "$lean:");
        assert!(names.get(0).unwrap().display.is_empty());
        let mut duplicate = name(1);
        // Display spelling and depth cannot make a canonical key distinct.
        duplicate.display = "another display".into();
        duplicate.depth = 3;
        assert!(names
            .push(duplicate)
            .unwrap_err()
            .contains("duplicate interned"));
        assert_eq!(names.len(), 2);
        assert!(names
            .push(Name {
                key: "$lean:".into(),
                display: "root".into(),
                depth: 1
            })
            .is_err());
    }
}

#[test]
fn hash_collisions_use_exact_keys_and_do_not_merge_symbols() {
    let mut names = Names::with_limit(0);
    let hash = 7;
    names.push_with_hash(name(1), hash).unwrap();
    names.push_with_hash(name(2), hash).unwrap();
    names.push_with_hash(name(3), hash).unwrap();
    assert_eq!(names.len(), 4);
    for id in 1..4 {
        assert_eq!(names.get(id).unwrap().as_ref(), &name(id));
    }
    assert!(names
        .push_with_hash(name(2), hash)
        .unwrap_err()
        .contains("duplicate interned"));
    assert_eq!(names.len(), 4);
}

#[test]
fn key_lookup_checks_each_collision_candidate_before_returning_a_name() {
    let mut names = Names::with_limit(0);
    names.push(name(1)).unwrap();
    names.push(name(2)).unwrap();
    // Model a hash collision without searching for a hasher preimage.
    let hash = names.fingerprint(&name(1).key);
    names.keys.insert(hash, Ids::Many(vec![2, 1]));
    assert_eq!(
        names.by_key(&name(1).key).unwrap().unwrap().as_ref(),
        &name(1)
    );
    assert!(names
        .push(name(1))
        .unwrap_err()
        .contains("duplicate interned"));
}

#[test]
fn largest_names_round_trip_and_invalid_codecs_fail_before_publication() {
    let boundary = Name {
        key: "k".repeat(MAX_PART_BYTES),
        display: "é".repeat(MAX_PART_BYTES / 2),
        depth: MAX_DEPTH,
    };
    let bytes = encode(&boundary).unwrap();
    assert_eq!(bytes.len(), MAX_RECORD);
    assert_eq!(decode(&bytes).unwrap(), boundary);
    let mut names = Names::with_limit(0);
    names.push(boundary.clone()).unwrap();
    assert_eq!(names.get(1).unwrap().as_ref(), &boundary);
    for field in 0..3 {
        let mut invalid = boundary.clone();
        match field {
            0 => invalid.key.push('!'),
            1 => invalid.display.push('!'),
            _ => invalid.depth += 1,
        }
        assert!(encode(&invalid).is_err());
        let previous = names.len();
        assert!(names.push(invalid).is_err());
        assert_eq!(names.len(), previous);
    }
    for length in 0..RECORD_HEADER {
        assert!(decode(&bytes[..length]).is_err());
    }
    let mut invalid = bytes.clone();
    invalid.push(0);
    assert!(decode(&invalid).is_err());
    let mut invalid = bytes.clone();
    invalid[2..6].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(decode(&invalid).is_err());
    let mut invalid = bytes.clone();
    invalid[RECORD_HEADER] = 255;
    assert!(decode(&invalid).is_err());
    let mut invalid = bytes.clone();
    invalid[..2].copy_from_slice(&257u16.to_le_bytes());
    assert!(decode(&invalid).is_err());
}

#[test]
fn invalid_scratch_index_ranges_lengths_and_reserved_bytes_fail_closed() {
    for case in 0..5 {
        let source = name(1);
        let bytes = encode(&source).unwrap();
        let mut data = Spool::new().unwrap();
        data.append(&bytes).unwrap();
        let mut index = [0u8; INDEX_BYTES];
        index[8..12].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
        match case {
            0 => index[..8].copy_from_slice(&u64::MAX.to_le_bytes()),
            1 => index[8..12].copy_from_slice(&0u32.to_le_bytes()),
            2 => index[8..12].copy_from_slice(&((MAX_RECORD + 1) as u32).to_le_bytes()),
            3 => index[15] = 1,
            _ => index[8..12].copy_from_slice(&((bytes.len() + 1) as u32).to_le_bytes()),
        }
        let mut positions = Spool::new().unwrap();
        positions.append(&index).unwrap();
        let spilled = Spilled {
            data: RefCell::new(data),
            index: RefCell::new(positions),
            count: 1,
        };
        assert!(spilled
            .get(0)
            .unwrap_err()
            .contains("invalid name scratch index"));
    }
}
