use super::*;

fn examples() -> Vec<Level> {
    vec![
        Level::number(0).unwrap(),
        Level::number(1).unwrap(),
        Level::number(65535).unwrap(),
        Level::variable("u".into()),
        Level::variable(String::new()),
        Level::variable("λ\0𝄞".into()).successor().unwrap(),
        Level::variable("u".into())
            .maximum(&Level::variable("v".into()))
            .unwrap(),
        Level::variable("u".into())
            .imax(&Level::variable("v".into()))
            .unwrap(),
        Level::from_storage_parts(vec![
            (Some("u".into()), vec![], 0),
            (Some("u".into()), vec!["u".into()], 1),
        ])
        .unwrap(),
        Level::from_storage_parts(vec![
            (None, vec!["g".into()], 2),
            (Some("u".into()), vec!["g".into(), "u".into()], 3),
        ])
        .unwrap(),
    ]
}

#[test]
fn exact_universe_representations_survive_without_normalization() {
    for level in examples() {
        let decoded = decode(&encode(&level).unwrap()).unwrap();
        assert_eq!(decoded, level);
        assert_eq!(decoded.storage_parts(), level.storage_parts());
    }
}

#[test]
fn paged_and_resident_values_weights_and_ids_match_across_page_boundaries() {
    let mut resident = Levels::with_limit(usize::MAX);
    let mut paged = Levels::with_limit(1024);
    for i in 0..900 {
        let value = Level::variable(format!("{}v{i}", "x".repeat(480)));
        resident.push(value.clone()).unwrap();
        paged.push(value).unwrap();
    }
    assert!(!resident.is_spilled());
    assert!(paged.is_spilled());
    for id in (0..paged.len()).rev().chain(0..paged.len()) {
        assert_eq!(resident.get(id).unwrap(), paged.get(id).unwrap());
        assert_eq!(
            paged.weight(id).unwrap(),
            resident.get(id).unwrap().memory_weight()
        );
    }
    assert!(paged.get(paged.len()).is_err());
    assert!(paged.weight(usize::MAX).is_err());
    assert_eq!(paged.get(0).unwrap().as_ref(), &Level::number(0).unwrap());
}

#[test]
fn selected_scratch_limit_pages_cold_reads_and_rejects_exhaustion() {
    let mut levels = Levels::with_storage_limits(0, 96);
    for i in 0..4 {
        levels.push(Level::number(i + 1).unwrap()).unwrap();
    }
    assert!(levels.is_spilled());
    assert_eq!(levels.get(1).unwrap().as_ref(), &Level::number(1).unwrap());
    assert_eq!(levels.get(4).unwrap().as_ref(), &Level::number(4).unwrap());
    let mut exhausted = false;
    for i in 5..30 {
        if levels.push(Level::number(i).unwrap()).is_err() {
            exhausted = true;
            break;
        }
    }
    assert!(exhausted);
}

#[test]
fn zero_limit_preserves_all_duplicate_ids_and_various_conditional_levels() {
    let mut levels = Levels::with_limit(0);
    let inputs = examples();
    for _ in 0..2 {
        for value in &inputs {
            levels.push(value.clone()).unwrap();
        }
    }
    assert!(levels.is_spilled());
    assert_eq!(levels.len(), 1 + inputs.len() * 2);
    for id in 1..levels.len() {
        assert_eq!(
            levels.get(id).unwrap().as_ref(),
            &inputs[(id - 1) % inputs.len()]
        );
    }
}

#[test]
fn recent_exact_values_share_bytes_but_preserve_ids_and_full_accounting() {
    let value = Level::variable("u".into());
    let mut levels = Levels::with_limit(0);
    levels.push(value.clone()).unwrap();
    let first_bytes = match &levels.0 {
        Storage::Spilled(s) => s.data.borrow().len(),
        _ => panic!("not spilled"),
    };
    for _ in 0..100 {
        levels.push(value.clone()).unwrap();
    }
    let Storage::Spilled(spilled) = &levels.0 else {
        panic!("not spilled")
    };
    assert_eq!(spilled.data.borrow().len(), first_bytes);
    assert_eq!(
        spilled.index.borrow().len(),
        levels.len() as u64 * INDEX_BYTES as u64
    );
    for id in 1..levels.len() {
        assert_eq!(levels.weight(id).unwrap(), value.memory_weight());
    }
    // Equal numeric meanings with different stored representations keep their
    // own bytes and weights. This cache does not normalize or compare meanings.
    let represented_zero = Level::from_storage_parts(vec![(None, vec![], 0)]).unwrap();
    assert_eq!(represented_zero.numeral(), Some(0));
    levels.push(represented_zero.clone()).unwrap();
    assert_eq!(levels.get(0).unwrap().storage_parts(), Vec::new());
    assert_eq!(
        levels.get(levels.len() - 1).unwrap().storage_parts(),
        represented_zero.storage_parts()
    );
    assert_eq!(levels.weight(0).unwrap(), 0);
    assert_eq!(levels.weight(levels.len() - 1).unwrap(), 96);
}

#[test]
fn recent_value_cache_stays_within_its_byte_and_entry_bounds() {
    let mut levels = Levels::with_limit(0);
    for index in 0..80 {
        levels
            .push(Level::variable(format!("v{index}{}", "x".repeat(16_000))))
            .unwrap();
        let Storage::Spilled(spilled) = &levels.0 else {
            panic!("not spilled")
        };
        assert!(spilled.recent.bytes <= RECENT_BYTES);
        assert!(spilled.recent.values.len() <= RECENT_ENTRIES);
    }
    for id in [0, 1, 40, 80] {
        assert!(levels.get(id).is_ok());
    }
}

#[test]
fn maximum_payload_is_accepted_and_one_extra_byte_rejects_before_insertion() {
    let boundary = Level::variable("v".repeat(MAX_WEIGHT - 96));
    assert_eq!(boundary.memory_weight(), MAX_WEIGHT);
    assert_eq!(decode(&encode(&boundary).unwrap()).unwrap(), boundary);
    let mut levels = Levels::with_limit(0);
    levels.push(boundary).unwrap();
    let too_large = Level::variable("v".repeat(MAX_WEIGHT - 95));
    assert!(levels.push(too_large.clone()).is_err());
    assert_eq!(levels.len(), 2);
    assert!(encode(&too_large).is_err());
    let mut hostile = vec![];
    hostile.extend_from_slice(&1u16.to_le_bytes());
    hostile.push(1);
    hostile.extend_from_slice(&((MAX_WEIGHT - 95) as u16).to_le_bytes());
    hostile.extend(std::iter::repeat_n(b'v', MAX_WEIGHT - 95));
    hostile.push(0);
    hostile.extend_from_slice(&0u32.to_le_bytes());
    assert!(decode(&hostile).unwrap_err().contains("payload limit"));
}

#[test]
fn malformed_counts_tags_lengths_utf8_offsets_and_ordering_reject() {
    assert!(decode(&[]).is_err());
    assert!(decode(&[0]).is_err());
    assert!(decode(&vec![0; MAX_RECORD + 1]).is_err());
    assert!(decode(&257u16.to_le_bytes()).is_err());
    assert!(decode(&[1, 0, 2, 0, 0, 0, 0, 0]).is_err());
    assert!(decode(&[1, 0, 0, 65, 0, 0, 0, 0]).is_err());
    let mut bytes = encode(&Level::variable("u".into())).unwrap();
    bytes[5] = 255;
    assert!(decode(&bytes).is_err());
    let mut bytes = encode(&Level::number(1).unwrap()).unwrap();
    let end = bytes.len();
    bytes[end - 4..].copy_from_slice(&65536u32.to_le_bytes());
    assert!(decode(&bytes).is_err());
    let mut bytes = encode(&Level::variable("u".into())).unwrap();
    bytes[3..5].copy_from_slice(&u16::MAX.to_le_bytes());
    assert!(decode(&bytes).is_err());
    let mut bytes = encode(&Level::number(0).unwrap()).unwrap();
    bytes.push(0);
    assert!(decode(&bytes).is_err());
    // Two individually valid monomials in descending order must not normalize
    // into an accepted alternative representation during restoration.
    let a = encode(&Level::variable("z".into())).unwrap();
    let b = encode(&Level::variable("a".into())).unwrap();
    let mut reversed = vec![2, 0];
    reversed.extend_from_slice(&a[2..]);
    reversed.extend_from_slice(&b[2..]);
    assert!(decode(&reversed).unwrap_err().contains("ordering"));
}

#[test]
fn invalid_scratch_metadata_ranges_and_changed_payload_weights_fail_closed() {
    for case in 0..5 {
        let value = Level::number(1).unwrap();
        let bytes = encode(&value).unwrap();
        let mut data = Spool::new().unwrap();
        data.append(&bytes).unwrap();
        let mut index = [0u8; INDEX_BYTES];
        index[8..12].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
        index[12..].copy_from_slice(&(value.memory_weight() as u32).to_le_bytes());
        match case {
            0 => index[..8].copy_from_slice(&u64::MAX.to_le_bytes()),
            1 => index[8..12].copy_from_slice(&0u32.to_le_bytes()),
            2 => index[8..12].copy_from_slice(&((MAX_RECORD + 1) as u32).to_le_bytes()),
            3 => index[12..].copy_from_slice(&((MAX_WEIGHT + 1) as u32).to_le_bytes()),
            _ => index[12..].copy_from_slice(&0u32.to_le_bytes()),
        }
        let mut positions = Spool::new().unwrap();
        positions.append(&index).unwrap();
        let spilled = Spilled {
            data: RefCell::new(data),
            index: RefCell::new(positions),
            count: 1,
            recent: Recent::default(),
        };
        assert!(spilled.get(0).is_err());
    }
}
