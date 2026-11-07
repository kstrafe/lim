//! Regressions for syntax comparison of identical shared subtrees.
use super::*;

fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}

fn tree_node(left: T, right: T) -> T {
    term(Term::Ctor {
        family: "Tree".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "node".into(),
        fields: vec![left, right],
    })
}

fn checked_tree() -> (Kernel, T) {
    let mut kernel = Kernel::new();
    kernel
        .inductive(
            "Tree",
            vec![],
            vec![],
            Level::number(1).unwrap(),
            vec![
                ("leaf".into(), vec![]),
                (
                    "node".into(),
                    vec![term(Term::SelfType), term(Term::SelfType)],
                ),
            ],
        )
        .unwrap();

    // A balanced perfect binary tree has 4,095 distinct constructor nodes.
    let mut layer = (0..2048)
        .map(|_| {
            term(Term::Ctor {
                family: "Tree".into(),
                levels: vec![],
                parameters: vec![],
                constructor: "leaf".into(),
                fields: vec![],
            })
        })
        .collect::<Vec<_>>();
    while layer.len() > 1 {
        layer = layer
            .chunks_exact(2)
            .map(|pair| tree_node(pair[0].clone(), pair[1].clone()))
            .collect();
    }
    let subtree = layer.pop().unwrap();
    kernel
        .definition(
            "checkedTree",
            vec![],
            global("Tree"),
            subtree.clone(),
            false,
        )
        .unwrap();
    kernel.reset_budget();
    (kernel, subtree)
}

#[test]
fn distinct_roots_compare_large_checked_shared_subtree_with_tiny_budget() {
    let (mut kernel, shared) = checked_tree();
    let left = tree_node(shared.clone(), shared.clone());
    let right = tree_node(shared.clone(), shared);
    kernel.budget = crate::ProofBudget::new(3, 256, 256).unwrap();
    assert!(kernel.same_syntax(&left, &right).unwrap());
}

#[test]
fn mismatch_in_left_child_survives_prior_shared_child_identity() {
    let (_kernel, shared) = checked_tree();
    let leaf = term(Term::Ctor {
        family: "Tree".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "leaf".into(),
        fields: vec![],
    });
    // The right child is popped first by the pending LIFO stack.
    let left = tree_node(leaf, shared.clone());
    let right = tree_node(shared.clone(), shared);
    assert!(!Kernel::new().same_syntax(&left, &right).unwrap());
}

#[test]
fn identity_of_unchecked_discarded_values_does_not_validate_definitions() {
    let mut kernel = Kernel::new();
    let unknown = global("missingGlobal");
    assert!(kernel.same_syntax(&unknown, &unknown).unwrap());
    assert!(kernel
        .definition(
            "badIdentityGlobal",
            vec![],
            term(Term::Sort(Level::number(1).unwrap())),
            unknown,
            false
        )
        .is_err());

    let ill_typed = term(Term::Let(
        global("#pt-nat"),
        term(Term::Sort(Level::number(1).unwrap())),
        term(Term::Ctor {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            constructor: "zero".into(),
            fields: vec![],
        }),
    ));
    assert!(kernel.same_syntax(&ill_typed, &ill_typed).unwrap());
    assert!(kernel
        .definition(
            "badIdentityDiscarded",
            vec![],
            global("#pt-nat"),
            ill_typed,
            false
        )
        .is_err());
}

#[test]
fn identity_still_observes_work_and_allocation_limits() {
    let value = term(Term::Var(0));
    let mut kernel = Kernel::with_budget(crate::ProofBudget::new(1, 128, 128).unwrap());
    kernel.work = kernel.budget.work();
    assert!(kernel
        .same_syntax(&value, &value)
        .unwrap_err()
        .contains("resource limit"));

    let mut kernel = Kernel::new();
    kernel.transformed_bytes = kernel.budget.phase_bytes() - 31;
    assert!(kernel
        .same_syntax(&value, &value)
        .unwrap_err()
        .contains("allocation limit"));
}
