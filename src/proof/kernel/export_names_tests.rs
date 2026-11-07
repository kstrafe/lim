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
    let mut eager = Names::with_limits(usize::MAX, usize::MAX);
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
fn value_and_candidate_limits_migrate_independently() {
    let mut value_only = Names::with_limits(0, usize::MAX);
    for id in 0..32 {
        value_only.push(name(id)).unwrap();
    }
    assert!(value_only.is_spilled());
    assert!(!value_only.candidates_spilled());

    let mut candidates_only = Names::with_limits(usize::MAX, 0);
    for id in 0..32 {
        candidates_only.push(name(id)).unwrap();
    }
    assert!(!candidates_only.is_spilled());
    assert!(candidates_only.candidates_spilled());
    for id in 0..32 {
        let value = name(id);
        assert_eq!(
            candidates_only
                .by_key(&value.key)
                .unwrap()
                .unwrap()
                .as_ref(),
            &value
        );
    }
}

#[test]
fn duplicate_keys_are_rejected_after_candidate_spilling() {
    let mut names = Names::with_limits(usize::MAX, 0);
    for id in 0..24 {
        names.push(name(id)).unwrap();
    }
    assert!(names.candidates_spilled());
    let mut duplicate = name(9);
    duplicate.display = "different display".into();
    duplicate.depth = 3;
    assert!(names
        .push(duplicate)
        .unwrap_err()
        .contains("duplicate interned"));
    assert_eq!(names.len(), 25);
}

#[test]
fn hash_collisions_use_exact_keys_and_preserve_reverse_candidate_order() {
    let mut names = Names::with_limit(0);
    let hash = 7;
    names.push_with_hash(name(1), hash).unwrap();
    names.push_with_hash(name(2), hash).unwrap();
    names.push_with_hash(name(3), hash).unwrap();
    assert_eq!(names.len(), 4);
    for id in 1..4 {
        assert_eq!(names.get(id).unwrap().as_ref(), &name(id));
    }
    assert_eq!(
        names
            .by_key_with_hash(&name(1).key, hash)
            .unwrap()
            .unwrap()
            .as_ref(),
        &name(1)
    );
    assert_eq!(
        names
            .by_key_with_hash(&name(2).key, hash)
            .unwrap()
            .unwrap()
            .as_ref(),
        &name(2)
    );
    assert!(names
        .push_with_hash(name(2), hash)
        .unwrap_err()
        .contains("duplicate interned"));
    assert_eq!(names.len(), 4);
}

#[test]
fn names_enforce_the_contiguous_id_cap_including_the_anonymous_root() {
    let mut names = Names::with_limit(usize::MAX);
    for id in 1..MAX_NAMES {
        names
            .push(Name {
                key: format!("n{id}"),
                display: String::new(),
                depth: 1,
            })
            .unwrap();
    }
    assert_eq!(names.len(), MAX_NAMES);
    assert!(names
        .push(name(1))
        .unwrap_err()
        .contains("name count limit"));
    assert_eq!(names.len(), MAX_NAMES);
    assert_eq!(
        names.get(MAX_NAMES - 1).unwrap().key,
        format!("n{}", MAX_NAMES - 1)
    );
}

#[test]
fn candidate_checksum_failure_poison_names_lookups_and_pushes() {
    let mut names = Names::with_limits(usize::MAX, 0);
    for id in 0..4097 {
        names.push(name(id)).unwrap();
    }
    assert!(names.candidates_spilled());
    let hash = names.keys.corrupt_first_flushed_record().unwrap();
    let key = "no-name-is-needed-to-traverse-the-corrupted-bucket";
    assert!(names
        .by_key_with_hash(&key, hash)
        .unwrap_err()
        .contains("checksum"));
    assert!(names.get(1).is_err());
    assert!(names.by_key(&key).is_err());
    assert!(names.push(name(5000)).is_err());
}

#[test]
fn invalid_value_index_read_poison_fails_closed() {
    let mut names = Names::with_limit(0);
    for id in 0..4097 {
        names.push(name(id)).unwrap();
    }
    let Storage::Spilled(storage) = &mut names.storage else {
        unreachable!()
    };
    storage
        .index
        .get_mut()
        .overwrite_flushed(0, &u64::MAX.to_le_bytes())
        .unwrap();
    assert!(names.get(0).unwrap_err().contains("checksum"));
    assert!(names.get(1).unwrap_err().contains("invalid after"));
    assert!(names.by_key("missing").is_err());
    assert!(names.push(name(5000)).is_err());
}

#[test]
fn long_unicode_and_deep_names_round_trip_after_spilling() {
    let mut names = Names::with_limits(0, 0);
    for id in 0..16 {
        names.push(name(id)).unwrap();
    }
    let boundary = Name {
        key: format!("$lean:{}", "命題.λ𝄞".repeat(1000)),
        display: format!("深い.名前.{}", "é".repeat(5000)),
        depth: MAX_DEPTH,
    };
    names.push(boundary.clone()).unwrap();
    assert!(names.is_spilled());
    assert!(names.candidates_spilled());
    assert_eq!(
        names.by_key(&boundary.key).unwrap().unwrap().as_ref(),
        &boundary
    );
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
fn selected_count_limit_includes_the_anonymous_root() {
    let mut names = Names::with_count_limit(1);
    assert_eq!(names.len(), 1);
    assert!(names.push(name(1)).unwrap_err().contains("count limit"));
    assert_eq!(names.len(), 1);
}
