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
        Ok(self
            .reduction_probe(depth, |kernel| {
                kernel.natural_closed_number(family, value, depth + 1)
            })?
            .flatten())
    }
}

#[cfg(test)]
#[path = "natural_probe_tests.rs"]
mod tests;
