use super::*;

fn sample() -> Declaration {
    let shared = term(Term::Var(0));
    let body = term(Term::Pair(
        shared.clone(),
        shared.clone(),
        term(Term::Var(1)),
    ));
    Declaration {
        universes: vec!["u".into()],
        ty: term(Term::Pi(shared.clone(), body.clone())),
        value: Some(body),
        family: None,
    }
}
fn declaration(t: T) -> Declaration {
    Declaration {
        universes: vec![],
        ty: t,
        value: None,
        family: None,
    }
}

#[test]
fn declaration_roundtrip_preserves_metadata_and_shared_dag() {
    let d = sample();
    let bytes = encode(&d).unwrap();
    let restored = decode(&bytes).unwrap();
    assert_eq!(restored.universes, d.universes);
    assert!(!Arc::ptr_eq(&restored.ty, restored.value.as_ref().unwrap()));
    let Term::Pi(a, p) = restored.ty.as_ref() else {
        panic!("wrong root")
    };
    let Term::Pair(x, y, _) = p.as_ref() else {
        panic!("wrong pair")
    };
    assert!(Arc::ptr_eq(a, x));
    assert!(Arc::ptr_eq(x, y));
    assert!(weight(&d).unwrap() >= bytes.len());
}

#[test]
fn malformed_headers_tags_refs_and_payloads_are_rejected() {
    assert!(decode(&[]).is_err());
    let mut bad_tag = encode(&declaration(term(Term::Var(0)))).unwrap();
    bad_tag[12] = 255;
    assert!(decode(&bad_tag).is_err());
    let mut bad_count = encode(&declaration(term(Term::Var(0)))).unwrap();
    bad_count[4..8].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(decode(&bad_count).is_err());
    let mut trailing = encode(&declaration(term(Term::Var(0)))).unwrap();
    trailing.push(0);
    assert!(decode(&trailing).is_err());
    let mut forward = encode(&declaration(term(Term::First(term(Term::Var(0)))))).unwrap();
    // The second record is First(child=0); change its backward child to itself.
    forward[22..26].copy_from_slice(&1u32.to_le_bytes());
    assert!(decode(&forward).is_err());
    let mut utf8 = encode(&declaration(term(Term::Global("x".into(), vec![])))).unwrap();
    utf8[17] = 255;
    assert!(decode(&utf8).is_err());
    let mut natural = encode(&declaration(term(Term::NatLiteral {
        family: "N".into(),
        value: Natural::parse("1").unwrap(),
    })))
    .unwrap();
    let natpos = natural.iter().position(|b| *b == b'1').unwrap();
    natural[natpos] = b'a';
    assert!(decode(&natural).is_err());
    let mut level = encode(&declaration(term(Term::Sort(Level::variable("u".into()))))).unwrap();
    level[17] = 2;
    assert!(decode(&level).is_err());
}

#[test]
fn byte_and_depth_limits_are_enforced() {
    assert!(decode(&vec![0; MAX_BYTES + 1]).is_err());
    let mut t = term(Term::Var(0));
    for _ in 0..=MAX_DEPTH {
        t = term(Term::First(t));
    }
    assert!(encode(&declaration(t)).is_err());
    let mut w = W(Vec::new());
    w.raw(MAGIC).unwrap();
    w.n(MAX_DEPTH + 2).unwrap();
    let mut leaf = W(Vec::new());
    leaf.u8(1).unwrap();
    leaf.n(0).unwrap();
    w.n(leaf.0.len()).unwrap();
    w.raw(&leaf.0).unwrap();
    for i in 0..=MAX_DEPTH {
        let mut node = W(Vec::new());
        node.u8(10).unwrap();
        node.id(i as u32).unwrap();
        w.n(node.0.len()).unwrap();
        w.raw(&node.0).unwrap();
    }
    w.ss(&[]).unwrap();
    w.id((MAX_DEPTH + 1) as u32).unwrap();
    w.u8(0).unwrap();
    w.u8(0).unwrap();
    assert!(decode(&w.0).is_err());
}

#[test]
fn exact_depth_boundary_and_shared_subtrees_use_their_full_height() {
    let mut root = term(Term::Var(0));
    for _ in 1..MAX_DEPTH {
        root = term(Term::First(root));
    }
    let original = declaration(root.clone());
    let decoded = decode(&encode(&original).unwrap()).unwrap();
    assert!(super::super::same_declaration(&original, &decoded).unwrap());
    assert!(weight(&original).is_ok());
    // The shared root has already been traversed as the type. Reusing it
    // beneath a fresh value node must still check its entire height.
    let too_deep = Declaration {
        universes: vec![],
        ty: root.clone(),
        value: Some(term(Term::First(root))),
        family: None,
    };
    assert!(encode(&too_deep).is_err());
    assert!(weight(&too_deep).is_err());
}

#[test]
fn every_term_tag_and_family_metadata_roundtrip() {
    let a = term(Term::Var(0));
    let b = term(Term::Var(3));
    let c = term(Term::SelfType);
    let l = Level::variable("u".into());
    let l2 = Level::number(2).unwrap();
    let terms: Vec<T> = vec![
        term(Term::Sort(l.clone())),
        a.clone(),
        term(Term::Global("g".into(), vec![l.clone()])),
        term(Term::NatLiteral {
            family: "N".into(),
            value: Natural::parse("12345678901234567890").unwrap(),
        }),
        term(Term::Pi(a.clone(), b.clone())),
        term(Term::Lam(b.clone(), c.clone())),
        term(Term::Let(a.clone(), b.clone(), c.clone())),
        term(Term::App(a.clone(), b.clone())),
        term(Term::Sigma(a.clone(), b.clone())),
        term(Term::Pair(a.clone(), b.clone(), a.clone())),
        term(Term::First(a.clone())),
        term(Term::Second(a.clone())),
        term(Term::Project {
            family: "F".into(),
            index: 2,
            subject: a.clone(),
        }),
        term(Term::Eq(a.clone(), b.clone(), a.clone())),
        term(Term::Refl(a.clone(), b.clone())),
        term(Term::QuotType(l.clone(), a.clone(), b.clone())),
        term(Term::QuotMake(l.clone(), a.clone(), b.clone(), a.clone())),
        term(Term::QuotLift {
            source_level: l.clone(),
            target_level: l2.clone(),
            ty: a.clone(),
            relation: b.clone(),
            target: c.clone(),
            function: b.clone(),
            respect: a.clone(),
            subject: c.clone(),
        }),
        term(Term::QuotInduct {
            level: l.clone(),
            ty: a.clone(),
            relation: b.clone(),
            motive: a.clone(),
            branch: b.clone(),
            subject: a.clone(),
        }),
        term(Term::EqElim {
            ty: a.clone(),
            left: b.clone(),
            motive: a.clone(),
            base: b.clone(),
            right: a.clone(),
            proof: b.clone(),
        }),
        term(Term::Ctor {
            family: "F".into(),
            levels: vec![l.clone()],
            parameters: vec![a.clone()],
            constructor: "C".into(),
            fields: vec![b.clone()],
        }),
        term(Term::Induct {
            family: "F".into(),
            levels: vec![l.clone()],
            parameters: vec![a.clone()],
            indices: vec![b.clone()],
            motive: a.clone(),
            branches: vec![b.clone()],
            subject: a.clone(),
        }),
        term(Term::MutualInduct {
            family: "F".into(),
            levels: vec![l.clone()],
            parameters: vec![a.clone()],
            indices: vec![b.clone()],
            cases: vec![RecursionCase {
                family: "G".into(),
                motive: a.clone(),
                branches: vec![b.clone()],
            }],
            subject: a.clone(),
        }),
        term(Term::NestedInduct {
            family: "F".into(),
            levels: vec![l.clone()],
            parameters: vec![a.clone()],
            selected: 1,
            indices: vec![b.clone()],
            cases: vec![NestedCase {
                selector: a.clone(),
                motive: b.clone(),
                branches: vec![a.clone()],
            }],
            subject: b.clone(),
        }),
        term(Term::SelfType),
        term(Term::SelfAt(vec![a.clone(), b.clone()])),
        term(Term::Recur("F".into(), vec![a.clone()])),
    ];
    assert_eq!(terms.len(), 27);
    for t in terms {
        let original = declaration(t);
        let bytes = encode(&original).unwrap();
        let decoded = decode(&bytes).unwrap();
        assert!(super::super::same_declaration(&original, &decoded).unwrap());
        assert_eq!(encode(&decoded).unwrap(), bytes);
    }
    let f = Family {
        group: vec!["F".into(), "G".into()],
        parameters: vec![a.clone()],
        indices: vec![b.clone()],
        sort: l2.clone(),
        large: true,
        constructors: vec![Constructor {
            name: "mkF".into(),
            fields: vec![a.clone()],
            recursive: vec![Some("G".into())],
            result_indices: vec![c.clone()],
        }],
    };
    let rich = Declaration {
        universes: vec!["u".into(), "v".into()],
        ty: a.clone(),
        value: Some(b.clone()),
        family: Some(f),
    };
    let bytes = encode(&rich).unwrap();
    let decoded = decode(&bytes).unwrap();
    assert!(super::super::same_declaration(&rich, &decoded).unwrap());
    assert_eq!(encode(&decoded).unwrap(), bytes);
    let family = decoded.family.unwrap();
    assert_eq!(family.group, vec!["F".to_string(), "G".to_string()]);
    assert!(family.large);
    assert_eq!(family.constructors[0].recursive, vec![Some("G".into())]);
}
