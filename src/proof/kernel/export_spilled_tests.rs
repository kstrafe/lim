use super::*;

fn same_expression(a: &Expression, b: &Expression) -> bool {
    match (a, b) {
        (Expression::Var(a), Expression::Var(b))
        | (Expression::Sort(a), Expression::Sort(b))
        | (Expression::Alias(a), Expression::Alias(b)) => a == b,
        (Expression::Global(an, aa), Expression::Global(bn, ba)) => an == bn && aa == ba,
        (Expression::App(aa, ab), Expression::App(ba, bb))
        | (Expression::Lam(aa, ab), Expression::Lam(ba, bb))
        | (Expression::Pi(aa, ab), Expression::Pi(ba, bb)) => aa == ba && ab == bb,
        (Expression::Let(aa, ab, ac), Expression::Let(ba, bb, bc))
        | (Expression::Project(aa, ab, ac), Expression::Project(ba, bb, bc)) => {
            aa == ba && ab == bb && ac == bc
        }
        (Expression::Natural(a), Expression::Natural(b)) => a == b,
        _ => false,
    }
}

fn entry(expression: Expression, id: usize) -> Entry {
    Entry {
        expression,
        depth: id % MAX_EXPRESSION_DEPTH + 1,
        payload: id * 17,
    }
}

#[test]
fn expression_codec_roundtrips_every_variant_and_u32_edges() {
    let high = u32::MAX as usize;
    let cases = [
        Expression::Var(high),
        Expression::Sort(high),
        Expression::Global(high, vec![]),
        Expression::Global(0, vec![0; 32]),
        Expression::App(0, 1),
        Expression::Lam(0, 1),
        Expression::Pi(0, 1),
        Expression::Let(0, 1, 2),
        Expression::Project(high, high, 0),
        Expression::Natural(Natural::parse("0").unwrap()),
        Expression::Natural(Natural::parse(&format!("1{}", "7".repeat(4095))).unwrap()),
        Expression::Alias(0),
    ];
    for (i, expression) in cases.iter().enumerate() {
        let bytes = encode(expression).unwrap();
        let decoded = decode(
            &bytes,
            if matches!(
                expression,
                Expression::App(..)
                    | Expression::Lam(..)
                    | Expression::Pi(..)
                    | Expression::Let(..)
                    | Expression::Alias(..)
                    | Expression::Project(..)
            ) {
                4
            } else {
                0
            },
        )
        .unwrap();
        assert!(same_expression(expression, &decoded), "variant {i}");
    }
}

#[test]
fn codec_rejects_malformed_records_and_forward_references() {
    let records: &[&[u8]] = &[
        &[],
        &[0],
        &[1, 0, 0],
        &[2, 0, 0, 0, 0],
        &[3, 0, 0, 0, 0, 0, 0, 0],
        &[4, 0, 0, 0, 0, 0, 0, 0],
        &[5, 0, 0, 0, 0, 0, 0, 0],
        &[6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        &[7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        &[8, 2, 0, b'1'],
        &[9, 0, 0, 0],
        &[99],
        &[0, 0, 0, 0, 0, 0],
        &[2, 0, 0, 0, 0, 33],
    ];
    for bytes in records {
        assert!(
            decode(bytes, 1).is_err(),
            "malformed tag {:?}",
            bytes.first()
        );
    }
    assert!(decode(&[3, 1, 0, 0, 0, 0, 0, 0, 0], 1).is_err());
    assert!(decode(&[9, 1, 0, 0, 0], 1).is_err());
    for natural in [
        "",
        "01",
        "+1",
        "-1",
        "１２",
        &format!("1{}", "0".repeat(4096)),
    ] {
        let mut record = vec![8];
        let text = natural.as_bytes();
        record.extend_from_slice(&(text.len() as u16).to_le_bytes());
        record.extend_from_slice(text);
        assert!(decode(&record, 0).is_err());
    }
    if usize::BITS > 32 {
        assert!(encode(&Expression::Var(u32::MAX as usize + 1)).is_err());
    }
}

#[test]
fn forced_spill_preserves_entries_metadata_aliases_and_cross_page_reads() {
    let count = 5000usize;
    let mut memory = Entries::with_limit(usize::MAX);
    let mut spilled = Entries::with_limit(0);
    let mut expected = Vec::with_capacity(count);
    for id in 0..count {
        let expression = match id % 5 {
            0 => Expression::Var((id * 7919) as usize),
            1 => Expression::Natural(Natural::parse(&(id * 13).to_string()).unwrap()),
            2 => Expression::Global((id % 97) as usize, vec![(id - 1) as usize]),
            3 => Expression::App(id - 1, (id - 2) as usize),
            _ => Expression::Alias((id / 2) as usize),
        };
        let value = entry(expression, id);
        expected.push(value.clone());
        memory.push(value.clone()).unwrap();
        spilled.push(value).unwrap();
    }
    assert!(spilled.is_spilled());
    assert_eq!(memory.len(), count);
    assert_eq!(spilled.len(), count);

    for id in (0..count)
        .step_by(37)
        .chain([count - 1, count - 2, 2047, 2048, 4095, 4096])
    {
        let a = memory.get(id).unwrap();
        let b = spilled.get(id).unwrap();
        assert!(same_expression(&a.expression, &expected[id].expression));
        assert!(same_expression(&a.expression, &b.expression), "entry {id}");
        assert_eq!(a.depth, b.depth);
        assert_eq!(a.payload, b.payload);
        let am = memory.meta(id).unwrap();
        let bm = spilled.meta(id).unwrap();
        assert_eq!(am.depth, bm.depth);
        assert_eq!(am.payload, bm.payload);
        assert_eq!(am.canonical, bm.canonical);
    }
    for id in [0, 2, 4, 999, 4999] {
        assert_eq!(
            spilled.meta(id).unwrap().canonical,
            match expected[id].expression {
                Expression::Alias(target) => target,
                _ => id,
            }
        );
    }
}
