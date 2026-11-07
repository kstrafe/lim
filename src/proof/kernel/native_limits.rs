//! Cumulative native proof-output limits, separate from kernel proof work,
//! fixed per-form syntax bounds and invocation-local resident cache budgets.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeProofLimits {
    pub max_bytes: usize,
    pub max_declarations: usize,
    /// Resident source-name/location directory accounting, not source bytes.
    pub max_directory_bytes: usize,
    pub max_render_nodes: usize,
    pub max_correspondence_nodes: usize,
    pub max_correspondence_bytes: usize,
    /// Capacity of each paged kernel store; source snapshots use `max_bytes`.
    pub max_scratch_bytes: u64,
}

impl Default for NativeProofLimits {
    fn default() -> Self {
        Self {
            max_bytes: super::native_source::SOURCE_BYTES,
            max_declarations: super::schedule::MAX_DECLARATIONS,
            max_directory_bytes: 32 * 1024 * 1024,
            max_render_nodes: 1_000_000,
            max_correspondence_nodes: 1_000_000,
            max_correspondence_bytes: 64 * 1024 * 1024,
            max_scratch_bytes: super::core::scratch::DEFAULT_BYTES,
        }
    }
}

impl NativeProofLimits {
    pub fn validate(self) -> Result<Self, String> {
        if self.max_bytes == 0 || self.max_bytes > isize::MAX as usize {
            return Err("native proof byte limit must be positive and fit a source offset".into());
        }
        if self.max_scratch_bytes == 0
            || self.max_scratch_bytes > super::core::scratch::MAX_SELECTED_BYTES
        {
            return Err(
                "native proof scratch byte limit must be positive and fit a source offset".into(),
            );
        }
        if self.max_declarations == 0 || u32::try_from(self.max_declarations).is_err() {
            return Err(format!(
                "native proof declaration limit must be between 1 and {}",
                u32::MAX
            ));
        }
        for (label, value) in [
            ("directory bytes", self.max_directory_bytes),
            ("render nodes", self.max_render_nodes),
            ("correspondence nodes", self.max_correspondence_nodes),
            ("correspondence bytes", self.max_correspondence_bytes),
        ] {
            if value == 0 {
                return Err(format!("native proof {label} limit must be positive"));
            }
        }
        Ok(self)
    }
}

impl std::fmt::Display for NativeProofLimits {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "bytes={} declarations={} directory-bytes={} render-nodes={} correspondence-nodes={} correspondence-bytes={} scratch-bytes={}", self.max_bytes, self.max_declarations, self.max_directory_bytes, self.max_render_nodes, self.max_correspondence_nodes, self.max_correspondence_bytes, self.max_scratch_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selected_limits_are_finite_positive_and_representable() {
        let defaults = NativeProofLimits::default();
        for field in 0..7 {
            let mut limits = defaults;
            match field {
                0 => limits.max_bytes = 0,
                1 => limits.max_declarations = 0,
                2 => limits.max_directory_bytes = 0,
                3 => limits.max_render_nodes = 0,
                4 => limits.max_correspondence_nodes = 0,
                5 => limits.max_correspondence_bytes = 0,
                _ => limits.max_scratch_bytes = 0,
            }
            assert!(limits.validate().is_err());
        }
        assert!(NativeProofLimits {
            max_bytes: usize::MAX,
            ..defaults
        }
        .validate()
        .is_err());
        if let Some(too_many) = (u32::MAX as usize).checked_add(1) {
            assert!(NativeProofLimits {
                max_declarations: too_many,
                ..defaults
            }
            .validate()
            .is_err());
        }
        assert_eq!(defaults.validate().unwrap(), defaults);
    }
}
