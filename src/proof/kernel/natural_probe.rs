//! Optional numeral normalization shares the enclosing proof's real budgets.
//! Declining a probe only returns to ordinary reduction, never proof acceptance.
use super::*;

impl Kernel {
    pub(super) fn natural_probe_number(
        &mut self,
        family: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<Natural>> {
        self.tick(depth)?;
        self.charge_transformation(0)?;
        let previous = self.natural_probe_budget;
        let mut budget = NaturalProbeBudget {
            work: self.work.saturating_add(16_384).min(WORK.saturating_sub(1)),
            bytes: self
                .transformed_bytes
                .saturating_add(2 * 1024 * 1024)
                .min(64 * 1024 * 1024 - 1),
            depth: depth.saturating_add(48).min(DEPTH - 1),
        };
        if let Some(parent) = previous {
            budget.work = budget.work.min(parent.work);
            budget.bytes = budget.bytes.min(parent.bytes);
            budget.depth = budget.depth.min(parent.depth);
        }
        self.natural_probe_budget = Some(budget);
        let result = self.natural_closed_number(family, value, depth + 1);
        self.natural_probe_budget = previous;
        match result {
            Err(why)
                if why == NATURAL_PROBE_DECLINED
                    || why == format!("natural arithmetic digit limit exceeded ({MAX_DIGITS})") =>
            {
                Ok(None)
            }
            result => result,
        }
    }
}

#[cfg(test)]
#[path = "natural_probe_tests.rs"]
mod tests;
