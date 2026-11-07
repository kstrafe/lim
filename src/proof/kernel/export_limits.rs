//! Selectable cumulative input limits, independent of logical authority,
//! per-record encoding bounds, resident table caches, and kernel work budgets.
use super::*;

/// Raw export resource limits. Larger values permit more input, never an
/// unchecked declaration. Paged stores keep their fixed resident budgets.
/// Every entry point validates these fields before reading any input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeanExportLimits {
    pub max_bytes: u64,
    /// Includes the built-in anonymous root (ID zero).
    pub max_names: usize,
    pub max_name_bytes: usize,
    /// Includes the built-in zero universe (ID zero).
    pub max_levels: usize,
    pub max_expressions: usize,
    pub max_declarations: usize,
    pub max_dependencies: usize,
    pub max_dependency_bytes: usize,
    pub max_payload_bytes: usize,
    /// Capacity of each paged raw-table/kernel backing file, not resident RAM.
    pub max_scratch_bytes: u64,
}

impl Default for LeanExportLimits {
    fn default() -> Self {
        Self {
            max_bytes: MAX_BYTES,
            max_names: MAX_NAMES,
            max_name_bytes: MAX_NAME_BYTES,
            max_levels: MAX_LEVELS,
            max_expressions: MAX_EXPRESSIONS,
            max_declarations: MAX_DECLARATIONS,
            max_dependencies: MAX_DEPENDENCIES,
            max_dependency_bytes: MAX_NAME_BYTES,
            max_payload_bytes: 64 * 1024 * 1024,
            max_scratch_bytes: spool::DEFAULT_BYTES,
        }
    }
}

impl LeanExportLimits {
    pub fn validate(self) -> std::result::Result<Self, String> {
        if self.max_bytes == 0 {
            return Err("export byte limit must be positive".into());
        }
        if self.max_scratch_bytes == 0 || self.max_scratch_bytes > spool::MAX_SELECTED_BYTES {
            return Err(
                "export scratch byte limit must be positive and fit a source offset".into(),
            );
        }
        for (name, value) in [
            ("name count", self.max_names),
            ("universe count", self.max_levels),
            ("expression count", self.max_expressions),
            ("declaration count", self.max_declarations),
            ("dependency count", self.max_dependencies),
        ] {
            if value == 0 || u32::try_from(value).is_err() {
                return Err(format!(
                    "export {name} limit must be between 1 and {}",
                    u32::MAX
                ));
            }
        }
        for (name, value) in [
            ("name bytes", self.max_name_bytes),
            ("dependency bytes", self.max_dependency_bytes),
            ("primitive payload bytes", self.max_payload_bytes),
        ] {
            if value == 0 {
                return Err(format!("export {name} limit must be positive"));
            }
        }
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_selected_limits_are_positive_and_counts_fit_protected_ids() {
        let defaults = LeanExportLimits::default();
        for field in 0..10 {
            let mut limits = defaults;
            match field {
                0 => limits.max_bytes = 0,
                1 => limits.max_names = 0,
                2 => limits.max_name_bytes = 0,
                3 => limits.max_levels = 0,
                4 => limits.max_expressions = 0,
                5 => limits.max_declarations = 0,
                6 => limits.max_dependencies = 0,
                7 => limits.max_dependency_bytes = 0,
                8 => limits.max_payload_bytes = 0,
                _ => limits.max_scratch_bytes = 0,
            }
            assert!(limits.validate().is_err(), "zero field {field}");
        }
        if let Some(too_large) = (u32::MAX as usize).checked_add(1) {
            for field in 0..5 {
                let mut limits = defaults;
                match field {
                    0 => limits.max_names = too_large,
                    1 => limits.max_levels = too_large,
                    2 => limits.max_expressions = too_large,
                    3 => limits.max_declarations = too_large,
                    _ => limits.max_dependencies = too_large,
                }
                assert!(limits.validate().is_err(), "oversized field {field}");
            }
        }
        assert_eq!(defaults.validate().unwrap(), defaults);
    }

    #[test]
    fn selected_maximum_byte_counters_reject_overflow_instead_of_saturating() {
        let mut replay = Replay::new();
        replay.limits.max_payload_bytes = usize::MAX;
        replay.payload_bytes = usize::MAX;
        let expression = crate::lsp::json::parse("{\"bvar\":0,\"ie\":0}").unwrap();
        assert!(replay
            .expression_record(&expression)
            .unwrap_err()
            .contains("overflow"));
        let level = crate::lsp::json::parse("{\"succ\":0,\"il\":1}").unwrap();
        assert!(replay
            .level_record(&level)
            .unwrap_err()
            .contains("overflow"));
        replay.limits.max_dependency_bytes = usize::MAX;
        replay.dependency_bytes = usize::MAX;
        let name = Name {
            key: "$lean:s1:x".into(),
            display: "x".into(),
            depth: 1,
        };
        assert!(replay
            .remember(&name, "theorem", vec![name.key.clone()])
            .unwrap_err()
            .contains("overflow"));
        assert_eq!(replay.reports.len(), 0);
    }
}
