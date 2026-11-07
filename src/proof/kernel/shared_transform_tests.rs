//! Regressions for operation-local memoization of shared transformation nodes.
use super::*;

fn var(index: usize) -> T {
    term(Term::Var(index))
}

fn lam(annotation: T, body: T) -> T {
    term(Term::Lam(annotation, body))
}

fn padding(depth: usize) -> T {
    if depth == 0 {
        var(0)
    } else {
        term(Term::App(padding(depth - 1), padding(depth - 1)))
    }
}

// Exercise the adaptive cache after the small-transform prefix. This padding
// is an unshared tree, so it cannot itself be compressed by memoization.
fn warmed(value: &T) -> T {
    term(Term::App(padding(6), value.clone()))
}

fn universe_warmed(value: &T) -> T {
    fn padding(depth: usize) -> T {
        if depth == 0 {
            term(Term::Sort(Level::variable("u".into())))
        } else {
            term(Term::App(padding(depth - 1), padding(depth - 1)))
        }
    }
    // Universe-independent padding is now shared without traversal. Use an
    // actually affected prefix to exercise the adaptive universe-copy cache.
    term(Term::App(padding(6), value.clone()))
}

fn result(value: T) -> T {
    let Term::App(_, result) = value.as_ref() else {
        panic!("expected App")
    };
    result.clone()
}

#[test]
fn nonzero_shift_preserves_shared_dag_outputs() {
    let mut kernel = Kernel::new();
    let shared = term(Term::App(var(0), var(2)));
    let input = term(Term::Pair(shared.clone(), shared.clone(), var(1)));

    let output = result(kernel.shift(&warmed(&input), 3, 0, 0).unwrap());
    let Term::Pair(left, right, tail) = output.as_ref() else {
        panic!("expected Pair")
    };
    assert!(Arc::ptr_eq(left, right));
    let expected = term(Term::App(var(3), var(5)));
    assert!(kernel.same_syntax(left, &expected).unwrap());
    assert!(kernel.same_syntax(tail, &var(4)).unwrap());
}

#[test]
fn shared_subtree_at_different_binder_depths_uses_distinct_indices() {
    let mut kernel = Kernel::new();
    let shared = term(Term::App(var(0), var(1)));
    let input = term(Term::Pair(
        term(Term::First(shared.clone())),
        lam(var(0), shared),
        var(0),
    ));

    let output = result(kernel.shift(&warmed(&input), 2, 0, 0).unwrap());
    let Term::Pair(shallow, deep, _) = output.as_ref() else {
        panic!("expected Pair")
    };
    let Term::Lam(_, deep_body) = deep.as_ref() else {
        panic!("expected Lam")
    };
    let Term::First(shallow) = shallow.as_ref() else {
        panic!("expected First")
    };
    // Both occurrences have the same absolute depth. Their binder counts
    // differ, so a cache keyed only by pointer and depth would be unsound.
    assert!(!Arc::ptr_eq(shallow, deep_body));
    assert!(kernel
        .same_syntax(shallow, &term(Term::App(var(2), var(3))))
        .unwrap());
    assert!(kernel
        .same_syntax(deep_body, &term(Term::App(var(0), var(3))))
        .unwrap());
}

#[test]
fn instantiate_arguments_and_universe_maps_are_isolated_between_calls() {
    let mut kernel = Kernel::new();
    let shared = term(Term::App(var(0), var(1)));
    let body = term(Term::Pair(shared.clone(), shared, var(2)));
    let first = result(kernel.instantiate(&warmed(&body), &var(4), 0).unwrap());
    kernel.reset_budget();
    let second = result(kernel.instantiate(&warmed(&body), &var(9), 0).unwrap());
    let first_child = term(Term::App(var(4), var(0)));
    let second_child = term(Term::App(var(9), var(0)));
    let first_expected = term(Term::Pair(first_child.clone(), first_child, var(1)));
    let second_expected = term(Term::Pair(second_child.clone(), second_child, var(1)));
    assert!(kernel.same_syntax(&first, &first_expected).unwrap());
    assert!(kernel.same_syntax(&second, &second_expected).unwrap());

    let u = Level::variable("u".into());
    let sort = term(Term::Sort(u));
    let body = term(Term::App(sort.clone(), sort));
    let mut first_map = HashMap::new();
    first_map.insert("u".into(), Level::number(2).unwrap());
    let mut second_map = HashMap::new();
    second_map.insert("u".into(), Level::number(7).unwrap());
    let first = result(
        kernel
            .universes(&universe_warmed(&body), &first_map, 0)
            .unwrap(),
    );
    kernel.reset_budget();
    let second = result(
        kernel
            .universes(&universe_warmed(&body), &second_map, 0)
            .unwrap(),
    );
    let Term::App(first_left, first_right) = first.as_ref() else {
        panic!("expected App")
    };
    let Term::App(second_left, second_right) = second.as_ref() else {
        panic!("expected App")
    };
    assert!(Arc::ptr_eq(first_left, first_right));
    assert!(Arc::ptr_eq(second_left, second_right));
    assert!(kernel
        .same_syntax(first_left, &term(Term::Sort(Level::number(2).unwrap())))
        .unwrap());
    assert!(kernel
        .same_syntax(second_left, &term(Term::Sort(Level::number(7).unwrap())))
        .unwrap());
}

#[test]
fn deeper_shared_occurrence_still_checks_recursion_depth() {
    let mut kernel = Kernel::new();
    let shared = term(Term::App(var(0), var(2)));
    let mut nested = shared.clone();
    for _ in 0..94 {
        nested = term(Term::First(nested));
    }
    let input = term(Term::Pair(shared, nested, var(0)));
    let error = kernel.shift(&warmed(&input), 1, 0, 0).unwrap_err();
    assert!(error.contains("recursion depth 97 > 96"), "{error}");
}

#[test]
fn memo_table_and_transformed_nodes_fit_a_small_proof_budget() {
    let mut kernel =
        Kernel::with_budget(crate::ProofBudget::new(10_000, 32 * 1024, 32 * 1024).unwrap());
    let shared = term(Term::App(var(0), var(2)));
    let input = term(Term::Pair(shared.clone(), shared, var(1)));
    let output = result(kernel.shift(&warmed(&input), 1, 0, 0).unwrap());
    assert!(
        kernel.transformation_bytes() > 0,
        "cache and output storage must be charged"
    );
    assert!(kernel.transformation_bytes() <= 32 * 1024);
    let Term::Pair(left, right, _) = output.as_ref() else {
        panic!("expected Pair")
    };
    assert!(Arc::ptr_eq(left, right));
}

#[test]
fn shared_invalid_terms_still_undergo_scope_validation() {
    let mut kernel = Kernel::new();
    let bad = term(Term::Global("missing-shared-global".into(), vec![]));
    let value = term(Term::Pair(
        bad.clone(),
        bad,
        term(Term::Sort(Level::number(0).unwrap())),
    ));
    let error = kernel
        .definition(
            "shared-invalid",
            vec![],
            term(Term::Sort(Level::number(1).unwrap())),
            value,
            false,
        )
        .unwrap_err();
    assert!(
        error.contains("unknown") || error.contains("declaration"),
        "{error}"
    );
    assert!(!kernel.contains("shared-invalid").unwrap());
}

#[test]
fn exponentially_shared_input_stays_a_small_transformed_dag() {
    let mut input = var(0);
    let mut expected = var(3);
    for _ in 0..48 {
        input = term(Term::App(input.clone(), input));
        expected = term(Term::App(expected.clone(), expected));
    }
    let mut kernel = Kernel::new();
    let output = kernel.shift(&input, 3, 0, 0).unwrap();
    assert!(
        kernel.work < 1000,
        "shared syntax must not expand into a tree"
    );
    assert!(kernel.transformation_bytes() < 32 * 1024);
    assert!(kernel.same_syntax(&output, &expected).unwrap());
}

#[test]
fn occurrence_sensitive_node_rewriters_are_not_memoized() {
    let shared = term(Term::App(var(0), var(1)));
    let input = term(Term::App(shared.clone(), shared.clone()));
    let mut visits = 0;
    let output = Kernel::new()
        .transform_nodes(
            &input,
            0,
            0,
            &mut |_, value, _, _| {
                if Arc::ptr_eq(value, &shared) {
                    visits += 1;
                    Ok(ControlFlow::Break(var(visits)))
                } else {
                    Ok(ControlFlow::Continue(value.clone()))
                }
            },
            &mut |_, index, _| Ok(var(index)),
            &mut |level| Ok(level.clone()),
        )
        .unwrap();
    assert_eq!(visits, 2);
    assert!(Kernel::new()
        .same_syntax(&output, &term(Term::App(var(1), var(2))))
        .unwrap());
}

#[test]
fn shared_transform_storage_exhaustion_fails_before_returning_a_result() {
    let shared = term(Term::App(var(0), var(1)));
    let input = term(Term::App(shared.clone(), shared));
    let mut kernel = Kernel::with_budget(crate::ProofBudget::new(100_000, 1, 1).unwrap());
    assert!(kernel
        .shift(&input, 1, 0, 0)
        .unwrap_err()
        .contains("allocation limit"));
}

#[test]
fn tiny_transform_avoids_memo_allocation() {
    let shared = term(Term::App(var(0), var(1)));
    let input = term(Term::App(shared.clone(), shared));
    let mut kernel = Kernel::new();
    let output = kernel.shift(&input, 1, 0, 0).unwrap();
    assert!(kernel.transformation_bytes() < 1024);
    let Term::App(left, right) = output.as_ref() else {
        panic!("expected App")
    };
    assert!(kernel.same_syntax(left, right).unwrap());
}

#[test]
fn memo_stops_growing_without_stopping_the_transformation() {
    let mut rows = (0..5000)
        .map(|_| {
            let shared = term(Term::App(var(0), var(1)));
            term(Term::App(shared.clone(), shared))
        })
        .collect::<Vec<_>>();
    while rows.len() > 1 {
        rows = rows
            .chunks(2)
            .map(|pair| {
                if pair.len() == 1 {
                    pair[0].clone()
                } else {
                    term(Term::App(pair[0].clone(), pair[1].clone()))
                }
            })
            .collect();
    }
    let mut memo = Some(TransformMemo::default());
    let mut kernel = Kernel::new();
    let output = kernel
        .transform_nodes_cached(
            &rows[0],
            0,
            0,
            &mut |_, value, _, _| Ok(ControlFlow::Continue(value.clone())),
            &mut |_, index, _| Ok(var(index + 1)),
            &mut |level| Ok(level.clone()),
            &mut memo,
        )
        .unwrap();
    assert_eq!(memo.unwrap().values.len(), 4096);
    let mut pending = vec![output];
    let mut variables = 0;
    while let Some(value) = pending.pop() {
        match value.as_ref() {
            Term::Var(index) => {
                assert!([1, 2].contains(index));
                variables += 1;
            }
            Term::App(left, right) => {
                pending.push(left.clone());
                pending.push(right.clone());
            }
            _ => panic!("unexpected transformed term"),
        }
    }
    assert_eq!(variables, 20_000);
}

#[test]
fn shared_shift_matches_uncached_transform_with_less_work_and_storage() {
    let mut input = var(0);
    for _ in 0..16 {
        input = term(Term::App(input.clone(), input));
    }
    let mut uncached = Kernel::new();
    let reference = uncached
        .transform(
            &input,
            0,
            0,
            &mut |_, index, binders| Ok(var(if index >= binders { index + 3 } else { index })),
            &mut |level| Ok(level.clone()),
        )
        .unwrap();
    let mut cached = Kernel::new();
    let output = cached.shift(&input, 3, 0, 0).unwrap();
    assert!(cached.work * 100 < uncached.work);
    assert!(cached.transformation_bytes() * 100 < uncached.transformation_bytes());
    // Comparing the complete resulting syntax also checks occurrences that
    // become shared. The comparison has its own unchanged resource budget.
    assert!(Kernel::new().same_syntax(&output, &reference).unwrap());
}
