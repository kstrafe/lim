use super::super::{Kernel, Level, NestedCase, RecursionCase, Term};
use super::{term, T};

fn v(index: usize) -> T {
    term(Term::Var(index))
}
fn s() -> Level {
    Level::number(0).unwrap()
}

// Let the kernel's syntax walker track binder depth. Returning the visited
// variable unchanged keeps the transformed tree irrelevant to this oracle.
fn oracle(value: &T) -> usize {
    let mut kernel = Kernel::new();
    let mut maximum = 0usize;
    kernel
        .transform_shared(
            value,
            0,
            0,
            &mut |_, index, binders| {
                if index >= binders {
                    maximum = maximum.max(index.saturating_sub(binders).saturating_add(1));
                }
                Ok(term(Term::Var(index)))
            },
            &mut |level| Ok(level.clone()),
        )
        .unwrap();
    maximum
}

fn assert_exact(value: T) {
    assert_eq!(value.loose_range(), oracle(&value), "{value:?}");
    let mut k = Kernel::new();
    let mut has_universes = false;
    k.transform_shared(
        &value,
        0,
        0,
        &mut |_, index, _| Ok(v(index)),
        &mut |level| {
            has_universes |= level.numeral().is_none();
            Ok(level.clone())
        },
    )
    .unwrap();
    assert_eq!(value.has_universe_params(), has_universes, "{value:?}");
}

#[test]
fn exact_ranges_cover_every_term_variant_and_child_position() {
    let examples = vec![
        term(Term::Sort(s())),
        v(2),
        term(Term::Global("g".into(), vec![s()])),
        term(Term::NatLiteral {
            family: "N".into(),
            value: super::super::Natural::parse("0").unwrap(),
        }),
        term(Term::Pi(v(2), v(3))),
        term(Term::Lam(v(4), v(5))),
        term(Term::Let(v(1), v(2), v(4))),
        term(Term::App(v(2), v(5))),
        term(Term::Sigma(v(3), v(4))),
        term(Term::Pair(v(1), v(3), v(5))),
        term(Term::First(v(2))),
        term(Term::Second(v(3))),
        term(Term::Project {
            family: "F".into(),
            index: 0,
            subject: v(4),
        }),
        term(Term::Eq(v(1), v(2), v(6))),
        term(Term::Refl(v(3), v(5))),
        term(Term::QuotType(s(), v(1), v(4))),
        term(Term::QuotMake(s(), v(2), v(5), v(7))),
        term(Term::QuotLift {
            source_level: s(),
            target_level: s(),
            ty: v(1),
            relation: v(2),
            target: v(3),
            function: v(4),
            respect: v(5),
            subject: v(6),
        }),
        term(Term::QuotInduct {
            level: s(),
            ty: v(1),
            relation: v(2),
            motive: v(3),
            branch: v(4),
            subject: v(5),
        }),
        term(Term::EqElim {
            ty: v(1),
            left: v(2),
            motive: v(3),
            base: v(4),
            right: v(5),
            proof: v(6),
        }),
        term(Term::Ctor {
            family: "F".into(),
            levels: vec![s()],
            parameters: vec![v(1), v(3)],
            constructor: "c".into(),
            fields: vec![v(5), v(7)],
        }),
        term(Term::Induct {
            family: "F".into(),
            levels: vec![s()],
            parameters: vec![v(1)],
            indices: vec![v(2)],
            motive: v(3),
            branches: vec![v(4), v(5)],
            subject: v(6),
        }),
        term(Term::MutualInduct {
            family: "F".into(),
            levels: vec![s()],
            parameters: vec![v(1)],
            indices: vec![v(2)],
            cases: vec![RecursionCase {
                family: "G".into(),
                motive: v(3),
                branches: vec![v(4), v(5)],
            }],
            subject: v(6),
        }),
        term(Term::NestedInduct {
            family: "F".into(),
            levels: vec![s()],
            selected: 0,
            parameters: vec![v(1)],
            indices: vec![v(2)],
            cases: vec![NestedCase {
                selector: v(3),
                motive: v(4),
                branches: vec![v(5)],
            }],
            subject: v(6),
        }),
        term(Term::SelfType),
        term(Term::SelfAt(vec![v(2), v(4)])),
        term(Term::Recur("F".into(), vec![v(3), v(5)])),
    ];
    for value in examples {
        assert_exact(value.clone());
        // Isolate each child marker so a larger variable in a later field
        // cannot conceal an omitted earlier field in the cached summary.
        for marker in 0..=7 {
            let mut k = Kernel::new();
            let isolated = k
                .transform_shared(
                    &value,
                    0,
                    0,
                    &mut |_, index, _| {
                        Ok(if index == marker {
                            v(index)
                        } else {
                            term(Term::Sort(s()))
                        })
                    },
                    &mut |level| Ok(level.clone()),
                )
                .unwrap();
            assert_exact(isolated);
            let injected = k
                .transform_shared(
                    &value,
                    0,
                    0,
                    &mut |_, index, _| {
                        Ok(term(Term::Sort(if index == marker {
                            Level::variable("u".into())
                        } else {
                            s()
                        })))
                    },
                    &mut |level| Ok(level.clone()),
                )
                .unwrap();
            assert_exact(injected);
        }
        // Isolate every own universe slot, including both lift levels.
        for marker in 0..=7 {
            let mut k = Kernel::new();
            let mut at = 0;
            let injected = k
                .transform_shared(
                    &value,
                    0,
                    0,
                    &mut |_, _, _| Ok(term(Term::Sort(s()))),
                    &mut |_| {
                        let level = if at == marker {
                            Level::variable("u".into())
                        } else {
                            s()
                        };
                        at += 1;
                        Ok(level)
                    },
                )
                .unwrap();
            assert_exact(injected);
        }
    }
}

#[test]
fn binder_offsets_and_nested_let_bodies_match_walker() {
    for (index, expected) in [(0, 0), (1, 0), (2, 1), (3, 2)] {
        let body = term(Term::Pi(term(Term::Sort(s())), v(index)));
        let outer = term(Term::Let(
            term(Term::Sort(s())),
            term(Term::Sort(s())),
            body,
        ));
        assert_eq!(outer.loose_range(), expected);
        assert_eq!(outer.loose_range(), oracle(&outer));
    }
    let closed = term(Term::Lam(term(Term::Sort(s())), v(0)));
    assert_eq!(closed.loose_range(), 0);
    let escaped = term(Term::Lam(term(Term::Sort(s())), v(1)));
    assert_eq!(escaped.loose_range(), 1);
    let sentinel = term(Term::Pi(term(Term::Sort(s())), v(usize::MAX)));
    assert_eq!(sentinel.loose_range(), usize::MAX);
    let nested = term(Term::Lam(term(Term::Sort(s())), sentinel));
    assert_eq!(nested.loose_range(), usize::MAX);
    assert!(nested.loose_range() >= oracle(&nested));
}
