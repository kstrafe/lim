use std::{fs, path::Path, process::Command};

fn diagnostic(source: &str, path: &Path, cache: &Path) -> lim::Diagnostic {
    lim::compile_source_to_assembly(
        source,
        path,
        &lim::CompileConfig::default(),
        cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

#[test]
fn declaration_failures_select_occurrences_deterministically() {
    let directory =
        std::env::temp_dir().join(format!("lim-declaration-spans-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("input.lim");
    let cache = directory.join("cache");
    for (source, expected) in [
        (
            "(#struct Value () ())\n(#struct Value () ())\n(#struct Value () ())",
            "Value",
        ),
        (
            "(#let cOUNT #u64 1u64)\n(#let cOUNT #u64 2u64)\n(#let cOUNT #u64 3u64)",
            "cOUNT",
        ),
    ] {
        let expected_start = source.match_indices(expected).nth(1).unwrap().0;
        fs::write(&path, source).unwrap();
        let error = diagnostic(source, &path, &cache);
        assert_eq!(
            error.span.unwrap().start,
            expected_start,
            "{}",
            error.message
        );
        let root = directory.join("root.lim");
        let root_source = format!("(#alias {expected} = ./input.lim::{expected})");
        fs::write(&root, &root_source).unwrap();
        let error = diagnostic(&root_source, &root, &cache);
        assert_eq!(error.span.unwrap().start, expected_start);
        assert!(error.source_name.unwrap().ends_with("input.lim"));
        let mut previous = None;
        for _ in 0..4 {
            let output = Command::new(env!("CARGO_BIN_EXE_lim"))
                .arg("--emit-asm")
                .arg(&root)
                .arg(directory.join("output.s"))
                .output()
                .unwrap();
            assert!(!output.status.success());
            if let Some(previous) = &previous {
                assert_eq!(previous, &output.stderr);
            }
            previous = Some(output.stderr);
        }
    }
    let source = "(#struct Value () ())\n(#unsafe-impl #send Value)\n(#unsafe-impl #sync Value)\n(#unsafe-impl #send Value)\n(#unsafe-impl #send Value)";
    let error = diagnostic(source, &path, &cache);
    assert_eq!(
        error.span.unwrap().start,
        source.match_indices("Value").nth(3).unwrap().0
    );

    let source = "(#fn worker () #u64 (#return 0u64))\n(#generate #thread-spawn (: task First : worker worker))\n(#generate #thread-spawn (: task Second : worker worker))\n(#struct Invalid () ((second First) (first Second)))";
    let expected = source.find("second First").unwrap() + "second ".len();
    for _ in 0..4 {
        let error = diagnostic(source, &path, &cache);
        assert_eq!(error.span.unwrap().start, expected, "{}", error.message);
    }
    fs::remove_dir_all(directory).unwrap();
}
