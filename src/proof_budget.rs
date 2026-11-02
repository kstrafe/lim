//! Explicit accounting limits; none grants a mathematical assumption.

/// Work and transformation traffic allowed while checking mathematical proofs.
/// These counters are separate from live process memory, time, parser limits,
/// recursion depth and the policy authorizing logical foundations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProofBudget {
    work: usize,
    phase_bytes: usize,
    total_bytes: usize,
}

impl Default for ProofBudget {
    fn default() -> Self {
        Self {
            work: 200_000,
            phase_bytes: 64 * 1024 * 1024,
            total_bytes: 256 * 1024 * 1024,
        }
    }
}

impl ProofBudget {
    /// Choose finite positive counters. The maxima bound configuration itself;
    /// a host memory/CPU guard is still needed for demanding proof replays.
    pub fn new(work: usize, phase_bytes: usize, total_bytes: usize) -> Result<Self, String> {
        for (label, value, maximum) in [
            ("proof work", work, 100_000_000u64),
            ("proof phase bytes", phase_bytes, 1u64 << 30),
            ("proof total bytes", total_bytes, 64u64 << 30),
        ] {
            if value == 0 || value as u64 > maximum {
                return Err(format!("{label} must be between 1 and {maximum}"));
            }
        }
        Ok(Self {
            work,
            phase_bytes,
            total_bytes,
        })
    }

    #[inline(always)]
    pub const fn work(&self) -> usize {
        self.work
    }
    #[inline(always)]
    pub const fn phase_bytes(&self) -> usize {
        self.phase_bytes
    }
    #[inline(always)]
    pub const fn total_bytes(&self) -> usize {
        self.total_bytes
    }

    pub(crate) fn json(self) -> crate::lsp::json::Json {
        use crate::lsp::json::Json;
        Json::Object(
            [
                ("work_per_phase".into(), Json::Number(self.work.to_string())),
                (
                    "transformation_bytes_per_phase".into(),
                    Json::Number(self.phase_bytes.to_string()),
                ),
                (
                    "transformation_bytes_total".into(),
                    Json::Number(self.total_bytes.to_string()),
                ),
            ]
            .into_iter()
            .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn budgets_are_positive_finite_and_default_to_existing_limits() {
        let default = ProofBudget::default();
        assert_eq!(
            default,
            ProofBudget::new(200_000, 64 << 20, 256 << 20).unwrap()
        );
        for arguments in [
            (0, 1, 1),
            (1, 0, 1),
            (1, 1, 0),
            (100_000_001, 1, 1),
            (1, (1 << 30) + 1, 1),
            (usize::MAX, 1, 1),
        ] {
            assert!(ProofBudget::new(arguments.0, arguments.1, arguments.2).is_err());
        }
        assert!(ProofBudget::new(1, 1, 1).is_ok());
        // A cumulative counter may intentionally be smaller than one phase.
        assert!(ProofBudget::new(100, 1000, 10).is_ok());
    }
}
