//! Configured budgets retain the kernel's checks and nested probe accounting.
use super::*;

fn larger() -> crate::ProofBudget {
    crate::ProofBudget::new(1_000_000, 128 << 20, 1 << 30).unwrap()
}

#[test]
fn probes_use_the_selected_work_limit_and_keep_spent_work() {
    let mut k = Kernel::with_budget(larger());
    k.work = WORK;
    let before = k.work;
    let result = k
        .reduction_probe(0, |k| {
            k.tick(0)?;
            Ok(7)
        })
        .unwrap();
    assert_eq!(result, Some(7));
    assert!(k.work > before);
    assert!(k.reduction_probe_budget.is_none());
    k.reset_budget();
    assert_eq!(k.work, 0);
    assert_eq!(k.budget, larger());
}

#[test]
fn selected_work_and_phase_limits_fail_at_their_actual_boundary() {
    let mut k = Kernel::with_budget(crate::ProofBudget::new(27, 100, 1000).unwrap());
    k.work = 26;
    k.tick(0).unwrap();
    let error = k.charge_work(1).unwrap_err();
    assert!(error.contains("28 > 27 work units"), "{error}");
    k.reset_budget();
    k.charge_transformation(100).unwrap();
    let error = k.charge_transformation(1).unwrap_err();
    assert!(error.contains("101 > 100 bytes"), "{error}");
    assert_eq!(k.transformed_bytes, 101);
}

#[test]
fn probes_can_cross_the_old_phase_limit_but_not_the_selected_one() {
    let mut k = Kernel::with_budget(larger());
    k.transformed_bytes = 64 << 20;
    let before = k.transformed_bytes;
    assert_eq!(
        k.reduction_probe(0, |k| k.charge_transformation(32))
            .unwrap(),
        Some(())
    );
    assert!(k.transformed_bytes > before);
    assert!(k.reduction_probe_budget.is_none());
    k.transformed_bytes = larger().phase_bytes();
    assert!(k
        .charge_transformation(1)
        .unwrap_err()
        .contains("allocation limit"));
}

#[test]
fn minimal_positive_budgets_decline_without_unsigned_underflow() {
    for budget in [
        crate::ProofBudget::new(1, 1000, 1000).unwrap(),
        crate::ProofBudget::new(1000, 1, 1000).unwrap(),
    ] {
        let mut k = Kernel::with_budget(budget);
        let result = k
            .reduction_probe(0, |k| {
                k.tick(0)?;
                k.charge_transformation(1)
            })
            .unwrap();
        assert_eq!(result, None);
        assert!(k.reduction_probe_budget.is_none());
        assert!(k.work > 0);
    }
}

#[test]
fn larger_budget_still_has_the_original_recursion_depth_limit() {
    let mut k = Kernel::with_budget(larger());
    let error = k.tick(DEPTH + 1).unwrap_err();
    assert!(error.contains("recursion depth 97 > 96"), "{error}");
}
