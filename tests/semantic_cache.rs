mod support;

use lim::{CompileConfig, TargetDescription};
use std::{fs, path::Path};

const LIB: &str = "(#fn identity (: value (#ref #u64)) (#ref #u64) (#return value))";
const MAIN: &str = "(#import \"lib.lim\")
  (#fn main () #u64 (#let value #u64 42u64)
    (#return (#deref (#call identity (: value (#borrow value))))))";

fn compile(
    directory: &Path,
    source: &str,
    config: &CompileConfig,
) -> (Result<String, lim::Diagnostic>, String) {
    lim::with_cache_report(|| {
        lim::compile_source_with_generated_sources(
            source,
            &directory.join("main.lim"),
            config,
            &directory.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
            None,
            &directory.join("generated"),
        )
    })
}
fn files(directory: &Path) -> Vec<std::path::PathBuf> {
    let mut paths = fs::read_dir(directory.join("cache/semantic"))
        .unwrap()
        .map(|p| p.unwrap().path())
        .collect::<Vec<_>>();
    paths.sort();
    paths
}
fn semantic_decisions(report: &str, decision: &str) -> usize {
    report
        .split("\"kind\":\"semantic-summary\"")
        .skip(1)
        .filter(|part| {
            part.split('}')
                .next()
                .unwrap()
                .contains(&format!("\"decision\":\"{decision}\""))
        })
        .count()
}

#[test]
fn warm_cache_reuses_both_modes_without_rewriting_and_preserves_assembly() {
    let scratch = support::Scratch::new("semantic-warm");
    let dir = scratch.path();
    fs::write(dir.join("lib.lim"), LIB).unwrap();
    let (cold, report) = compile(dir, MAIN, &CompileConfig::default());
    assert_eq!(semantic_decisions(&report, "miss"), 2, "{report}");
    let path = files(dir).pop().unwrap();
    let bytes = fs::read(&path).unwrap();
    let modified = fs::metadata(&path).unwrap().modified().unwrap();
    let (warm, report) = compile(dir, MAIN, &CompileConfig::default());
    assert_eq!(semantic_decisions(&report, "hit"), 2, "{report}");
    assert_eq!(cold.unwrap(), warm.unwrap());
    assert_eq!(fs::read(&path).unwrap(), bytes);
    assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);
}

#[test]
fn imported_word_writer_retains_real_loans_on_cache_hits() {
    let scratch = support::Scratch::new("semantic-word-loans");
    let dir = scratch.path();
    fs::write(
        dir.join("lib.lim"),
        "(#struct Holder (: value (#ref #u64)))
         (#fn store (: words (#slice-mut #u64) : source (#ref #u64)) ()
           (#unsafe (#word-write Holder words (#struct-literal Holder (: value source))))
           (#return ()))",
    )
    .unwrap();
    let source = "(#import \"lib.lim\")
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#call store (: words (#borrow-slice-mut words 1usize 2usize) : source (#borrow seed)))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice words 1usize 2usize))))
        (#let result #u64 (#deref (#get copied value)))
        (#forget copied) (#forget words) (#set seed 0u64) (#return result))";
    let config = CompileConfig::default();
    let (cold, _) = compile(dir, source, &config);
    let (warm, report) = compile(dir, source, &config);
    assert_eq!(cold.unwrap(), warm.unwrap());
    assert!(semantic_decisions(&report, "hit") > 0, "{report}");
    let invalid = source.replace("(#let result", "(#set seed 0u64) (#let result");
    let cold_error = compile(dir, &invalid, &config).0.unwrap_err();
    let (warm, report) = compile(dir, &invalid, &config);
    let warm_error = warm.unwrap_err();
    assert_eq!(cold_error.code, lim::DiagnosticCode::Borrow);
    assert_eq!(cold_error, warm_error);
    // Invalid programs never publish a reusable summary artifact.
    assert_eq!(semantic_decisions(&report, "hit"), 0, "{report}");
}

#[test]
fn imported_word_reader_checks_required_loans_after_cache_hits() {
    let scratch = support::Scratch::new("semantic-word-reader");
    let dir = scratch.path();
    fs::write(
        dir.join("lib.lim"),
        "(#struct Holder (: value (#ref #u64)))
         (#fn read (: words (#slice #u64)) #u64
           (#let restored Holder (#unsafe (#word-read Holder words)))
           (#let answer #u64 (#deref (#get restored value)))
           (#forget restored) (#return answer))",
    )
    .unwrap();
    let source = "(#import \"lib.lim\")
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder (: value (#borrow seed)))))
        (#let answer #u64 (#call read (: words (#borrow-slice words))))
        (#forget words) (#return answer))";
    let config = CompileConfig::default();
    let (cold, _) = compile(dir, source, &config);
    let (warm, report) = compile(dir, source, &config);
    assert_eq!(cold.unwrap(), warm.unwrap());
    assert!(semantic_decisions(&report, "hit") > 0, "{report}");
    let invalid = source.replace(
        "(#let answer",
        "(#unsafe (#word-write #u64 (#borrow-slice-mut words) 0u64)) (#let answer",
    );
    let cold_error = compile(dir, &invalid, &config).0.unwrap_err();
    let warm_error = compile(dir, &invalid, &config).0.unwrap_err();
    assert_eq!(cold_error, warm_error);
    assert_eq!(cold_error.code, lim::DiagnosticCode::Linear);
}

#[test]
fn transitive_dependency_root_cfg_and_type_changes_invalidate() {
    let scratch = support::Scratch::new("semantic-invalidation");
    let dir = scratch.path();
    fs::write(dir.join("lib.lim"), "(#import \"dep.lim\")").unwrap();
    fs::write(dir.join("dep.lim"), LIB).unwrap();
    let config = CompileConfig::default();
    compile(dir, MAIN, &config).0.unwrap();
    assert!(semantic_decisions(&compile(dir, MAIN, &config).1, "hit") > 0);
    fs::write(dir.join("dep.lim"), format!("{LIB}\n; dependency changed")).unwrap();
    let (result, report) = compile(dir, MAIN, &config);
    result.unwrap();
    assert_eq!(semantic_decisions(&report, "hit"), 0);
    assert!(semantic_decisions(&report, "miss") > 0);
    let mut changed_cfg = config.clone();
    changed_cfg.set("unused-key", "changed");
    let (result, report) = compile(dir, MAIN, &changed_cfg);
    result.unwrap();
    assert_eq!(semantic_decisions(&report, "hit"), 0);
    let (result, report) = compile(dir, &MAIN.replace("42u64", "43u64"), &config);
    result.unwrap();
    assert_eq!(semantic_decisions(&report, "hit"), 0);
    fs::write(
        dir.join("dep.lim"),
        format!("(#struct Added (: value #u64)) {LIB}"),
    )
    .unwrap();
    let (result, report) = compile(dir, MAIN, &config);
    result.unwrap();
    assert_eq!(semantic_decisions(&report, "hit"), 0);
    assert_eq!(files(dir).len(), 5);
}

#[test]
fn invalid_library_is_not_published_and_borrow_diagnostic_is_identical() {
    let scratch = support::Scratch::new("semantic-invalid");
    let dir = scratch.path();
    fs::write(
        dir.join("lib.lim"),
        "(#fn identity (: value (#ref #u64)) (#ref #u64)
        (#let local #u64 0u64) (#return (#borrow local)))",
    )
    .unwrap();
    let (first, _) = compile(dir, MAIN, &CompileConfig::default());
    let first = first.unwrap_err();
    assert_eq!(first.code, lim::DiagnosticCode::Borrow);
    assert!(!dir.join("cache/semantic").exists());
    let (second, report) = compile(dir, MAIN, &CompileConfig::default());
    let second = second.unwrap_err();
    assert_eq!(first.message, second.message);
    assert_eq!(first.span, second.span);
    assert_eq!(semantic_decisions(&report, "hit"), 0);
}

#[test]
fn corrupt_and_unknown_schema_artifacts_fall_back_to_analysis() {
    let scratch = support::Scratch::new("semantic-corrupt");
    let dir = scratch.path();
    fs::write(dir.join("lib.lim"), LIB).unwrap();
    let expected = compile(dir, MAIN, &CompileConfig::default()).0.unwrap();
    let path = files(dir).pop().unwrap();
    let good = fs::read(&path).unwrap();
    let mut bad_checksum = good.clone();
    *bad_checksum.last_mut().unwrap() ^= 128;
    let mut bad_schema = good.clone();
    bad_schema[0] = b'?';
    for bad in [good[..good.len() / 2].to_vec(), bad_schema, bad_checksum] {
        fs::write(&path, bad).unwrap();
        let (result, report) = compile(dir, MAIN, &CompileConfig::default());
        assert_eq!(result.unwrap(), expected);
        assert_eq!(semantic_decisions(&report, "hit"), 0);
        assert_eq!(fs::read(&path).unwrap(), good);
    }
}

#[test]
fn unavailable_cache_and_programs_without_imports_still_compile() {
    let scratch = support::Scratch::new("semantic-unavailable");
    let dir = scratch.path();
    let plain = "(#fn main () #u64 (#return 42u64))";
    compile(dir, plain, &CompileConfig::default()).0.unwrap();
    assert!(!dir.join("cache/semantic").exists());
    fs::write(dir.join("lib.lim"), LIB).unwrap();
    fs::write(dir.join("cache"), "not a directory").unwrap();
    compile(dir, MAIN, &CompileConfig::default()).0.unwrap();
}

#[test]
fn aggregate_outcomes_and_mutable_reference_stores_match_cold_analysis() {
    let scratch = support::Scratch::new("semantic-aggregate");
    let dir = scratch.path();
    fs::write(
        dir.join("lib.lim"),
        "(#struct Holder (: value (#ref #u64)))
      (#enum Choice ((Found Holder) Missing))
      (#fn choose (: owner (#ref #u64) : flag #bool) Choice
        (#return (#if flag (Found (#struct-literal Holder (: value owner))) Missing)))
      (#fn replace (: slot (#ref-mut (#ref #u64)) : value (#ref #u64)) ()
        (#deref-set slot value) (#return ()))",
    )
    .unwrap();
    let source = "(#import \"lib.lim\") (#fn main () #u64
      (#let-mut first #u64 1u64) (#let second #u64 42u64)
      (#let-mut holder Holder (#struct-literal Holder (: value (#borrow first))))
      (#call replace (: slot (#borrow-mut (#get holder value)) : value (#borrow second)))
      (#set first 2u64)
      (#let result #u64 (#match (#call choose (: owner (#get holder value) : flag true))
        (#case (Found selected) (#block (#let answer #u64 (#deref (#get selected value)))
          (#forget selected) answer))
        (#case Missing 0u64))) (#forget holder) (#return result))";
    let cold = compile(dir, source, &CompileConfig::default()).0.unwrap();
    let (warm, report) = compile(dir, source, &CompileConfig::default());
    assert_eq!(warm.unwrap(), cold);
    assert_eq!(semantic_decisions(&report, "hit"), 4, "{report}");
}

#[test]
fn generated_dependency_changes_invalidate_semantic_summaries() {
    let scratch = support::Scratch::new("semantic-generated");
    let dir = scratch.path();
    let library = "(#gn functions () `((#fn generated () #u64 (#return 7u64)))) (@functions)";
    fs::write(dir.join("lib.lim"), library).unwrap();
    let source = "(#import \"lib.lim\") (#fn main () #u64 (#return (#call generated ())))";
    let cold = compile(dir, source, &CompileConfig::default()).0.unwrap();
    let (warm, report) = compile(dir, source, &CompileConfig::default());
    assert_eq!(warm.unwrap(), cold);
    assert!(semantic_decisions(&report, "hit") > 0, "{report}");
    fs::write(dir.join("lib.lim"), library.replace("7u64", "8u64")).unwrap();
    let (changed, report) = compile(dir, source, &CompileConfig::default());
    assert_ne!(changed.unwrap(), cold);
    assert_eq!(semantic_decisions(&report, "hit"), 0, "{report}");
}

#[test]
fn standard_library_summaries_warm_without_skipping_validation() {
    let scratch = support::Scratch::new("semantic-std");
    let source = "(#std) (#fn main () #u64 (#return 42u64))";
    let cold = compile(scratch.path(), source, &CompileConfig::default())
        .0
        .unwrap();
    let (warm, report) = compile(scratch.path(), source, &CompileConfig::default());
    assert_eq!(warm.unwrap(), cold);
    assert!(semantic_decisions(&report, "hit") > 100, "{report}");
    assert_eq!(semantic_decisions(&report, "miss"), 0, "{report}");
}

#[test]
fn check_and_emission_use_separate_target_contexts() {
    let scratch = support::Scratch::new("semantic-check");
    let dir = scratch.path();
    fs::write(dir.join("lib.lim"), LIB).unwrap();
    let config = CompileConfig::default();
    let check = || {
        lim::with_cache_report(|| {
            lim::check_source_with_generated_sources(
                MAIN,
                &dir.join("main.lim"),
                &config,
                &dir.join("cache"),
                &dir.join("generated"),
            )
        })
    };
    check().0.unwrap();
    let (result, report) = check();
    result.unwrap();
    assert_eq!(semantic_decisions(&report, "hit"), 2);
    let (result, report) = compile(dir, MAIN, &config);
    result.unwrap();
    assert_eq!(semantic_decisions(&report, "hit"), 0);
    assert_eq!(files(dir).len(), 2);
}

#[test]
fn concurrent_compilations_publish_complete_identical_artifacts() {
    let scratch = support::Scratch::new("semantic-concurrent");
    let dir = scratch.path();
    fs::write(dir.join("lib.lim"), LIB).unwrap();
    let barrier = std::sync::Barrier::new(4);
    let results = std::thread::scope(|scope| {
        let workers = (0..4)
            .map(|_| {
                scope.spawn(|| {
                    barrier.wait();
                    compile(dir, MAIN, &CompileConfig::default()).0.unwrap()
                })
            })
            .collect::<Vec<_>>();
        workers
            .into_iter()
            .map(|worker| worker.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert!(results.iter().all(|assembly| assembly == &results[0]));
    assert_eq!(files(dir).len(), 1);
    let (warm, report) = compile(dir, MAIN, &CompileConfig::default());
    assert_eq!(warm.unwrap(), results[0]);
    assert_eq!(semantic_decisions(&report, "hit"), 2);
}
