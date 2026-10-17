//! Current-compilation invocation mappings, independent of persisted headers.
use std::{
    cell::RefCell,
    collections::BTreeSet,
    path::{Path, PathBuf},
};

use crate::{CompileConfig, Diagnostic, Span};

#[derive(Debug)]
struct Artifact {
    source: PathBuf,
    invocation: Span,
    path: PathBuf,
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

pub(crate) fn record(invocation: Span, source_paths: &[PathBuf], path: &Path) {
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
    Ok(artifacts
        .into_iter()
        .filter(|artifact| {
            let span = artifact.invocation;
            artifact.source == selected
                && if start == end {
                    span.start <= start && start < span.end
                } else {
                    start < end && start < span.end && span.start < end
                }
        })
        .map(|artifact| artifact.path)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect())
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
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn identical_invocations_keep_every_full_span_and_warm_files() {
        let scratch = Scratch::new();
        let source = "(#gn make (name) `((#type ,name #u64)))\n(@make\n Shared) (@make\n Shared)";
        let first = source.find("(@make").unwrap();
        let second = source.rfind("(@make").unwrap();
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
            first + "(@make\n ".len(),
            second,
            second + "(@make\n ".len(),
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
        let source = "(#gn inner () `((@#optional (: type #u64 : name Shared))))\n\
            (#gn outer () `((@inner) (@#optional (: type #u64 : name OuterOnly))))\n\
            (#gn other () `((@inner)))\n(@outer)\n(@other)\n(@other)";
        for _ in 0..2 {
            let outer = source.find("(@outer)").unwrap();
            let paths = scratch.lookup(source, outer, outer);
            assert_eq!(paths.len(), 4, "{paths:?}");
            for position in [
                source.find("(@other)").unwrap(),
                source.rfind("(@other)").unwrap(),
            ] {
                let other = scratch.lookup(source, position, position);
                assert_eq!(other.len(), 3, "{other:?}");
                assert_eq!(other.iter().filter(|path| paths.contains(path)).count(), 2);
                assert!(other.iter().all(|path| path.is_file()));
            }
        }
    }

    #[test]
    fn changed_input_does_not_return_old_artifacts() {
        let scratch = Scratch::new();
        let old = "(@#optional (: type #u64 : name Old))";
        let new = "(@#optional (: type #u64 : name New))";
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
            "(#cfg-if (#cfg-is #platform lookup-excluded) (@#optional (: type #u64 : name Hidden)))";
        let position = source.find("(@#optional").unwrap();
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
            record(span, &paths, Path::new("first.lim"));
            let _ = std::panic::catch_unwind(|| {
                with_artifacts(|| {
                    record(span, &paths, Path::new("inner.lim"));
                    panic!("restore observer");
                })
            });
            record(span, &paths, Path::new("last.lim"));
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
