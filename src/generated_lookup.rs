//! Current-compilation invocation mappings, independent of persisted headers.
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use crate::{CompileConfig, Diagnostic, Span};

#[derive(Debug)]
struct Artifact {
    source: PathBuf,
    invocation: Span,
    path: PathBuf,
    generator: String,
    nested: bool,
}

/// A generated file selected from the current compilation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedArtifact {
    pub path: PathBuf,
    /// The actual generating invocation's name, without `#generate` (including any `#`).
    pub generator: String,
    pub nested: bool,
}

thread_local! {
    static ARTIFACTS: RefCell<Option<Vec<Artifact>>> = const { RefCell::new(None) };
}

pub(crate) fn enabled() -> bool {
    ARTIFACTS.with(|artifacts| artifacts.borrow().is_some())
}

fn with_artifacts<R>(operation: impl FnOnce() -> R) -> (R, Vec<Artifact>) {
    struct Restore(Option<Vec<Artifact>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            ARTIFACTS.with(|artifacts| artifacts.replace(self.0.take()));
        }
    }
    let _restore = Restore(ARTIFACTS.with(|artifacts| artifacts.replace(Some(Vec::new()))));
    let result = operation();
    let artifacts = ARTIFACTS.with(|artifacts| artifacts.borrow_mut().take().unwrap());
    (result, artifacts)
}

pub(crate) fn record(
    invocation: Span,
    source_paths: &[PathBuf],
    path: &Path,
    generator: &str,
    nested: bool,
) {
    ARTIFACTS.with(|artifacts| {
        let mut artifacts = artifacts.borrow_mut();
        let Some(artifacts) = artifacts.as_mut() else {
            return;
        };
        let Some(source) = source_paths.get(invocation.source_id as usize) else {
            return;
        };
        artifacts.push(Artifact {
            source: crate::editor::path_key(source),
            invocation,
            path: path.to_owned(),
            generator: generator.to_owned(),
            nested,
        });
    });
}

/// Check the current source and locate generated files for invocations selected
/// in `selected_path`. Offsets are bytes: an equal pair selects a point within
/// an invocation; otherwise the half-open range selects overlapping invocations.
/// Cache and generated files are materialized under the entry's parent `.lim`.
pub fn locate_generated(
    source: &str,
    entry: &Path,
    config: &CompileConfig,
    selected_path: &Path,
    start: usize,
    end: usize,
) -> Result<Vec<PathBuf>, Diagnostic> {
    Ok(
        locate_generated_details(source, entry, config, selected_path, start, end)?
            .into_iter()
            .map(|artifact| artifact.path)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
    )
}

/// Like [`locate_generated`], including generating names and whether each file
/// was generated through a nested invocation. Direct matches win when a path
/// has multiple origins. Results sort direct first, then by path.
pub fn locate_generated_details(
    source: &str,
    entry: &Path,
    config: &CompileConfig,
    selected_path: &Path,
    start: usize,
    end: usize,
) -> Result<Vec<GeneratedArtifact>, Diagnostic> {
    let entry = crate::editor::path_key(entry);
    let directory = entry.parent().unwrap_or(Path::new(".")).join(".lim");
    let (result, artifacts) = with_artifacts(|| {
        crate::check_source_with_generated_sources(
            source,
            &entry,
            config,
            &directory.join("cache"),
            &directory.join("generated"),
        )
    });
    result?;
    let selected = crate::editor::path_key(selected_path);
    let mut selected_artifacts = BTreeMap::<PathBuf, GeneratedArtifact>::new();
    for artifact in artifacts.into_iter().filter(|artifact| {
        let span = artifact.invocation;
        artifact.source == selected
            && if start == end {
                span.start <= start && start < span.end
            } else {
                start < end && start < span.end && span.start < end
            }
    }) {
        let details = GeneratedArtifact {
            path: artifact.path,
            generator: artifact.generator,
            nested: artifact.nested,
        };
        selected_artifacts
            .entry(details.path.clone())
            .and_modify(|previous| {
                if !details.nested {
                    *previous = details.clone();
                }
            })
            .or_insert(details);
    }
    let mut details = selected_artifacts.into_values().collect::<Vec<_>>();
    details.sort_by(|a, b| a.nested.cmp(&b.nested).then_with(|| a.path.cmp(&b.path)));
    Ok(details)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "lim-generated-lookup-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn lookup(&self, source: &str, start: usize, end: usize) -> Vec<PathBuf> {
            let entry = self.0.join("main.lim");
            locate_generated(
                source,
                &entry,
                &CompileConfig::default(),
                &entry,
                start,
                end,
            )
            .unwrap()
        }
        fn details(&self, source: &str, start: usize, end: usize) -> Vec<GeneratedArtifact> {
            let entry = self.0.join("main.lim");
            locate_generated_details(
                source,
                &entry,
                &CompileConfig::default(),
                &entry,
                start,
                end,
            )
            .unwrap()
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn identical_invocations_keep_every_full_span_and_warm_files() {
        let scratch = Scratch::new();
        let source = "#gn make (name) `((#type ,name #u64))\n#generate make\n   Shared\n#generate make\n   Shared\n";
        let first = source.find("#generate make").unwrap();
        let second = source.rfind("#generate make").unwrap();
        let paths = scratch.lookup(source, first, first);
        assert_eq!(paths.len(), 1);
        assert!(paths[0].starts_with(scratch.0.join(".lim/generated")));
        let timestamp =
            std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
        fs::OpenOptions::new()
            .write(true)
            .open(&paths[0])
            .unwrap()
            .set_times(fs::FileTimes::new().set_modified(timestamp))
            .unwrap();
        for start in [
            first + "#generate make\n   ".len(),
            second,
            second + "#generate make\n   ".len(),
        ] {
            assert_eq!(scratch.lookup(source, start, start), paths);
        }
        assert_eq!(scratch.lookup(source, first, source.len()), paths);
        assert_eq!(
            fs::metadata(&paths[0]).unwrap().modified().unwrap(),
            timestamp
        );
        assert!(scratch
            .lookup(source, source.len(), source.len())
            .is_empty());
        assert!(scratch.lookup(source, first - 1, first).is_empty());
    }

    #[test]
    fn nested_reused_generators_include_all_child_artifacts() {
        let scratch = Scratch::new();
        let source = "#gn inner () `((#generate #optional ((type #u64) (name Shared))))
#gn outer () `((#generate inner) (#generate #optional ((type #u64) (name OuterOnly))))
#gn other () `((#generate inner))\n#generate outer\n#generate other\n#generate other\n";
        for _ in 0..2 {
            let outer = source.find("(#generate outer)").unwrap();
            let paths = scratch.lookup(source, outer, outer);
            assert_eq!(paths.len(), 4, "{paths:?}");
            for position in [
                source.find("(#generate other)").unwrap(),
                source.rfind("(#generate other)").unwrap(),
            ] {
                let other = scratch.lookup(source, position, position);
                assert_eq!(other.len(), 3, "{other:?}");
                assert_eq!(other.iter().filter(|path| paths.contains(path)).count(), 2);
                assert!(other.iter().all(|path| path.is_file()));
            }
        }
    }

    #[test]
    fn details_track_user_names_and_direct_origins_through_reuse_and_cache() {
        for calls in [
            "#generate outer\n#generate inner\n",
            "#generate inner\n#generate outer\n",
        ] {
            let scratch = Scratch::new();
            let source = format!(
                "#gn inner () `((#type Shared #u64))\n\
                 #gn outer () `((#generate inner))\n{calls}"
            );
            for _ in 0..2 {
                let outer = source.rfind("(#generate outer)").unwrap();
                let inner = source.rfind("(#generate inner)").unwrap();
                let details = scratch.details(&source, outer, outer);
                assert_eq!(details.len(), 2);
                assert_eq!(
                    (details[0].generator.as_str(), details[0].nested),
                    ("outer", false)
                );
                assert_eq!(
                    (details[1].generator.as_str(), details[1].nested),
                    ("inner", true)
                );
                let direct = scratch.details(&source, inner, inner);
                assert_eq!(direct.len(), 1);
                assert_eq!(
                    (direct[0].generator.as_str(), direct[0].nested),
                    ("inner", false)
                );
                assert_eq!(direct[0].path, details[1].path);
                let all = scratch.details(&source, 0, source.len());
                assert_eq!(all.len(), 2);
                assert!(all.iter().all(|artifact| !artifact.nested));
                assert!(all.windows(2).all(|pair| pair[0].path < pair[1].path));
                let mut paths = details
                    .into_iter()
                    .map(|artifact| artifact.path)
                    .collect::<Vec<_>>();
                paths.sort();
                assert_eq!(scratch.lookup(&source, outer, outer), paths);
            }
        }
    }

    #[test]
    fn details_track_builtin_origins_through_user_reuse_and_cache() {
        let builtin = "#generate #optional ((type #u64) (name Shared))\n";
        // Distinct inputs stay distinct even when both use the same builtin.
        let direct_builtin = "#generate #optional ((type #u64) (name Direct))\n";
        for calls in [
            format!("#generate outer\n#generate other\n#generate other\n{direct_builtin}"),
            format!("{direct_builtin}\n#generate outer\n#generate other\n#generate other\n"),
        ] {
            let scratch = Scratch::new();
            let source = format!(
                "#gn inner () `({builtin})\n\
                 #gn outer () `((#generate inner))\n\
                 #gn other () `((#generate inner))\n{calls}"
            );
            for _ in 0..2 {
                for caller in ["outer", "other"] {
                    let position = source.rfind(&format!("#generate {caller}\n")).unwrap();
                    let details = scratch.details(&source, position, position);
                    assert_eq!(details.len(), 3, "{details:?}");
                    assert_eq!(details[0].generator, caller);
                    assert!(!details[0].nested);
                    assert!(details[1..].iter().all(|artifact| artifact.nested));
                    assert!(details[1].path < details[2].path);
                    let helper = details
                        .iter()
                        .find(|artifact| artifact.generator == "#optional")
                        .unwrap();
                    let direct_position = source.rfind(direct_builtin).unwrap();
                    let direct = scratch.details(&source, direct_position, direct_position);
                    assert_eq!(direct.len(), 1);
                    assert_eq!(direct[0].generator, "#optional");
                    assert!(!direct[0].nested);
                    assert_ne!(direct[0].path, helper.path);
                    assert!(helper.nested);
                }
                let all = scratch.details(&source, 0, source.len());
                assert_eq!(all.len(), 5);
                assert_eq!(all.iter().filter(|artifact| !artifact.nested).count(), 3);
                assert!(all[3..].iter().all(|artifact| artifact.nested));
                assert!(all[3..]
                    .iter()
                    .any(|artifact| artifact.generator == "inner"));
                assert!(all[3..]
                    .iter()
                    .any(|artifact| artifact.generator == "#optional"));
                assert!(all[3].path < all[4].path);
                assert!(all[..3].windows(2).all(|pair| pair[0].path < pair[1].path));
            }
        }
    }

    #[test]
    fn changed_input_does_not_return_old_artifacts() {
        let scratch = Scratch::new();
        let old = "#generate #optional ((type #u64) (name Old))\n";
        let new = "#generate #optional ((type #u64) (name New))\n";
        let old_paths = scratch.lookup(old, 0, old.len());
        let new_paths = scratch.lookup(new, 0, new.len());
        assert_eq!(old_paths.len(), 1);
        assert_eq!(new_paths.len(), 1);
        assert_ne!(old_paths, new_paths);
        assert!(old_paths[0].is_file());
        assert!(fs::read_to_string(&new_paths[0]).unwrap().contains("New"));
    }

    #[test]
    fn cfg_excluded_invocations_have_no_matches() {
        let scratch = Scratch::new();
        let source =
            "#cfg-if (#cfg-is #platform lookup-excluded) (#generate #optional ((type #u64) (name Hidden)))\n";
        let position = source.find("#generate #optional").unwrap();
        let entry = scratch.0.join("main.lim");
        let mut enabled = CompileConfig::default();
        enabled.set("platform", "lookup-excluded");
        let previous =
            locate_generated(source, &entry, &enabled, &entry, position, position).unwrap();
        assert_eq!(previous.len(), 1);
        assert!(scratch.lookup(source, position, position).is_empty());
        assert!(previous[0].is_file());
    }

    #[test]
    fn scoped_recording_restores_outer_observer_after_panic() {
        assert!(!enabled());
        let span = Span::new(0, 5, 1, 1);
        let paths = vec![PathBuf::from("main.lim")];
        let (_, artifacts) = with_artifacts(|| {
            assert!(enabled());
            record(span, &paths, Path::new("first.lim"), "first", false);
            let _ = std::panic::catch_unwind(|| {
                with_artifacts(|| {
                    record(span, &paths, Path::new("inner.lim"), "inner", true);
                    panic!("restore observer");
                })
            });
            record(span, &paths, Path::new("last.lim"), "last", false);
        });
        assert!(!enabled());
        assert_eq!(
            artifacts
                .iter()
                .map(|artifact| artifact.path.as_path())
                .collect::<Vec<_>>(),
            vec![Path::new("first.lim"), Path::new("last.lim")]
        );
    }
}
