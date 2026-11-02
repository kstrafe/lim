//! Optional reduction cannot extend the enclosing proof's real budgets.
//! Restore enclosing limits on every result, without refunding spent work or
//! allocations. Only exact internal refusals fall back to ordinary reduction;
//! unknown declarations, invalid universes and existing global failures escape.
use super::*;

impl Kernel {
    pub(super) fn reduction_probe<R>(
        &mut self,
        depth: usize,
        operation: impl FnOnce(&mut Self) -> Result<R>,
    ) -> Result<Option<R>> {
        self.tick(depth)?;
        self.charge_transformation(0)?;
        let previous = self.reduction_probe_budget;
        let mut budget = ReductionProbeBudget {
            work: self
                .work
                .saturating_add(16_384)
                .min(self.budget.work().saturating_sub(1)),
            bytes: self
                .transformed_bytes
                .saturating_add(2 * 1024 * 1024)
                .min(self.budget.phase_bytes().saturating_sub(1)),
            depth: depth.saturating_add(48).min(DEPTH - 1),
        };
        if let Some(parent) = previous {
            budget.work = budget.work.min(parent.work);
            budget.bytes = budget.bytes.min(parent.bytes);
            budget.depth = budget.depth.min(parent.depth);
        }
        self.reduction_probe_budget = Some(budget);
        let result = operation(self);
        self.reduction_probe_budget = previous;
        match result {
            Err(why)
                if why == REDUCTION_PROBE_DECLINED
                    || why
                        == format!(
                            "natural arithmetic digit limit exceeded ({})",
                            natural::MAX_DIGITS
                        ) =>
            {
                Ok(None)
            }
            result => result.map(Some),
        }
    }
}
