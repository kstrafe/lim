use super::*;

#[derive(Clone, Debug)]
enum Expression {
    Number(u32),
    Variable(usize),
    Successor(Box<Self>),
    Maximum(Box<Self>, Box<Self>),
    Imax(Box<Self>, Box<Self>),
}
const NAMES: [&str; 3] = ["u", "v", "w"];

impl Expression {
    fn evaluate(&self, values: &[u32; 3]) -> u32 {
        match self {
            Self::Number(n) => *n,
            Self::Variable(i) => values[*i],
            Self::Successor(a) => a.evaluate(values) + 1,
            Self::Maximum(a, b) => a.evaluate(values).max(b.evaluate(values)),
            Self::Imax(a, b) => {
                let right = b.evaluate(values);
                if right == 0 {
                    0
                } else {
                    a.evaluate(values).max(right)
                }
            }
        }
    }

    fn compile(&self) -> Result<Level> {
        match self {
            Self::Number(n) => Level::number(*n),
            Self::Variable(i) => Ok(Level::variable(NAMES[*i].into())),
            Self::Successor(a) => a.compile()?.successor(),
            Self::Maximum(a, b) => a.compile()?.maximum(&b.compile()?),
            Self::Imax(a, b) => a.compile()?.imax(&b.compile()?),
        }
    }
}

fn expressions() -> Vec<Expression> {
    let mut cases = (0..4)
        .map(|n| (Expression::Number(n), 0))
        .collect::<Vec<_>>();
    cases.extend((0..3).map(|v| (Expression::Variable(v), 0)));
    let mut seed = 0x5a61_1989u32;
    let mut next = || {
        seed = seed.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        seed as usize
    };
    for _ in 0..89 {
        let (a, ad) = cases[next() % cases.len()].clone();
        let (b, bd) = cases[next() % cases.len()].clone();
        let (expression, depth) = if ad.max(bd) >= 5 {
            (Expression::Variable(next() % 3), 0)
        } else {
            let expression = match next() % 3 {
                0 => Expression::Successor(Box::new(a)),
                1 => Expression::Maximum(Box::new(a), Box::new(b)),
                _ => Expression::Imax(Box::new(a), Box::new(b)),
            };
            (expression, ad.max(bd) + 1)
        };
        cases.push((expression, depth));
    }
    cases.into_iter().map(|(case, _)| case).collect()
}

#[test]
fn guarded_levels_match_an_independent_recursive_evaluator() {
    let assignments = [0, 1, 4];
    for expression in expressions() {
        let normalized = expression.compile().unwrap();
        for u in assignments {
            for v in assignments {
                for w in assignments {
                    let values = [u, v, w];
                    let map = NAMES
                        .iter()
                        .zip(values)
                        .map(|(name, value)| (name.to_string(), Level::number(value).unwrap()))
                        .collect();
                    let actual = normalized.substitute(&map).unwrap().numeral().unwrap();
                    assert_eq!(
                        actual,
                        expression.evaluate(&values),
                        "{expression:?}, {values:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn exact_order_equivalence_and_zero_implication_match_small_counterexample_bases() {
    // Offsets in this bounded corpus are below 16. A failing inequality has a
    // witness with every variable at 0 or 1 except one base made larger than
    // those offsets. This finite oracle is test-only; the checker is symbolic.
    let mut assignments = Vec::new();
    for u in [0, 1, 64] {
        for v in [0, 1, 64] {
            for w in [0, 1, 64] {
                assignments.push([u, v, w]);
            }
        }
    }
    let cases = expressions()
        .into_iter()
        .map(|expression| {
            assert!(expression.evaluate(&[1, 1, 1]) < 16);
            let level = expression.compile().unwrap();
            let values = assignments
                .iter()
                .map(|values| expression.evaluate(values))
                .collect::<Vec<_>>();
            (expression, level, values)
        })
        .collect::<Vec<_>>();
    for (a, left, lv) in &cases {
        for (b, right, rv) in &cases {
            let less = lv.iter().zip(rv).all(|(l, r)| l <= r);
            let same = lv == rv;
            let implication = lv.iter().zip(rv).all(|(l, r)| *l != 0 || *r == 0);
            assert_eq!(left.at_most(right).unwrap(), less, "{a:?} <= {b:?}");
            assert_eq!(left.equivalent(right).unwrap(), same, "{a:?} == {b:?}");
            assert_eq!(
                left.zero_implies_zero(right).unwrap(),
                implication,
                "{a:?}=0 implies {b:?}=0"
            );
        }
    }
}

#[test]
fn imax_is_not_max_and_conditional_offsets_survive_zero() {
    let u = Level::variable("u".into());
    let v = Level::variable("v".into());
    let zero = Level::number(0).unwrap();
    let one = Level::number(1).unwrap();
    assert!(u.imax(&zero).unwrap().zero());
    assert!(one.imax(&v).unwrap().equivalent(&v).unwrap());
    assert!(u.imax(&u).unwrap().equivalent(&u).unwrap());
    assert!(!u
        .imax(&v)
        .unwrap()
        .equivalent(&u.maximum(&v).unwrap())
        .unwrap());
    let successor = u.imax(&v).unwrap().successor().unwrap();
    let map = HashMap::from([("u".into(), Level::number(9).unwrap()), ("v".into(), zero)]);
    assert_eq!(successor.substitute(&map).unwrap().numeral(), Some(1));
    assert!(!u.zero_implies_zero(&one).unwrap());
    assert!(u.maximum(&v).unwrap().zero_implies_zero(&v).unwrap());
}

#[test]
fn universe_substitution_is_simultaneous_in_bases_and_guards() {
    let u = Level::variable("u".into());
    let v = Level::variable("v".into());
    let expression = u.imax(&v).unwrap();
    let one = Level::number(1).unwrap();
    let map = HashMap::from([("u".into(), v.clone()), ("v".into(), one.clone())]);
    let actual = expression.substitute(&map).unwrap();
    assert!(actual.equivalent(&v.maximum(&one).unwrap()).unwrap());
    assert!(actual.numeral().is_none());
    assert!(expression
        .substitute(&HashMap::from([("u".into(), one)]))
        .is_err());
}

#[test]
fn universe_limits_are_errors_rather_than_changed_truth_values() {
    assert!(Level::number(LEVEL).unwrap().successor().is_err());
    let mut guards = Level::number(1).unwrap();
    for i in 0..GUARDS {
        guards = guards.gated(&Level::variable(format!("v{i}"))).unwrap();
    }
    assert!(guards.gated(&Level::variable("overflow".into())).is_err());
    let mut terms = Level::number(0).unwrap();
    for i in 0..TERMS {
        terms = terms.maximum(&Level::variable(format!("v{i}"))).unwrap();
    }
    assert!(terms.maximum(&Level::variable("overflow".into())).is_err());
    let mut left = terms.clone();
    for offset in left.terms.values_mut() {
        *offset = 1;
    }
    let mut right = terms;
    for offset in right.terms.values_mut() {
        *offset = 2;
    }
    assert!(
        left.at_most(&right).is_err(),
        "comparison budget was ignored"
    );
}
