use super::*;

#[test]
fn storage_round_trips_exact_level_representations() {
    let mut cases = vec![
        Level::number(0).unwrap(),
        Level::number(LEVEL).unwrap(),
        Level::variable("u".into()),
        Level::variable("λ".into()).successor().unwrap(),
        Level::variable("u".into())
            .maximum(&Level::variable("v".into()))
            .unwrap(),
    ];
    let gated = Level::variable("x".into())
        .imax(&Level::variable("g".into()))
        .unwrap();
    cases.push(gated);
    cases.push(
        Level::from_storage_parts(vec![
            (Some("x".into()), vec![], 0),
            (Some("x".into()), vec!["x".into()], 1),
        ])
        .unwrap(),
    );

    for level in cases {
        let parts = level.storage_parts();
        let restored = Level::from_storage_parts(parts.clone()).unwrap();
        assert_eq!(restored, level);
        assert_eq!(restored.storage_parts(), parts);
    }
}

#[test]
fn storage_accepts_empty_names_and_empty_representation() {
    let level = Level::from_storage_parts(vec![
        (None, vec![String::new()], 0),
        (Some(String::new()), vec![], 0),
    ]);
    assert!(level.is_ok());
    assert!(Level::from_storage_parts(Vec::new()).unwrap().zero());
    let level = Level::from_storage_parts(vec![(Some(String::new()), vec![], 0)]).unwrap();
    assert_eq!(
        level.storage_parts(),
        vec![(Some(String::new()), vec![], 0)]
    );
}

#[test]
fn storage_rejects_limits_and_noncanonical_ordering() {
    assert!(Level::from_storage_parts(vec![(None, vec![], LEVEL + 1)]).is_err());
    assert!(Level::from_storage_parts(vec![(None, vec!["x".into(); GUARDS + 1], 0)]).is_err());
    assert!(Level::from_storage_parts(
        (0..=TERMS)
            .map(|i| (Some(format!("v{i}")), vec![], 0))
            .collect()
    )
    .is_err());
    assert!(Level::from_storage_parts(vec![
        (Some("u".into()), vec![], 0),
        (Some("u".into()), vec![], 1),
    ])
    .is_err());
    assert!(Level::from_storage_parts(vec![
        (Some("v".into()), vec![], 0),
        (Some("u".into()), vec![], 0),
    ])
    .is_err());
    assert!(
        Level::from_storage_parts(vec![(Some("u".into()), vec!["z".into(), "a".into()], 0)])
            .is_err()
    );
    assert!(
        Level::from_storage_parts(vec![(Some("u".into()), vec!["a".into(), "a".into()], 0)])
            .is_err()
    );
}

#[test]
fn storage_rejects_name_payload_over_sixteen_mib() {
    let name = "n".repeat(16 * 1024 * 1024 + 1);
    assert!(Level::from_storage_parts(vec![(Some(name), vec![], 0)]).is_err());
}
