//! Exhaustive small access matrix: producer, caller, unrelated dependency.
mod support;
use std::{fs, path::Path};

fn write(root: &Path, path: &str, source: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn generated_file_access_is_exactly_definition_plus_invocation_not_dependencies() {
    let scratch = support::Scratch::new("generator-context-matrix");
    write(scratch.path(), "producer/lib.lim", "(#export make visible) (#fn hidden () #u64 (#return 42u64)) (#fn visible () #u64 (#return 42u64)) (#gn make (name text) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol text) ())))))");
    write(scratch.path(), "third/lib.lim", "(#export visible) (#fn hidden () #u64 (#return 42u64)) (#fn visible () #u64 (#return 42u64))");
    for prefix in ["one", "two"] {
        for (target, allowed) in [
            (format!("{prefix}@producer@hidden"), true),
            (format!("{prefix}@producer@visible"), true),
            (format!("{prefix}@hidden"), true),
            (format!("{prefix}@visible"), true),
            (format!("{prefix}@third@visible"), true),
            (format!("{prefix}@third@hidden"), false),
        ] {
            write(scratch.path(), "caller/lib.lim", &format!("(#export read visible) (#import-external \"../producer/lib.lim\" producer) (#import-external \"../third/lib.lim\" third) (#fn hidden () #u64 (#return 42u64)) (#fn visible () #u64 (#return 42u64)) (#generate producer@make read \"{target}\")"));
            let source = format!("(#import-external \"caller/lib.lim\" {prefix}) (#fn main () #u64 (#return (#call {prefix}@read ())))");
            for mode in 0..3 {
                let result = if mode == 0 {
                    lim::parse_program_from_path(&source, &scratch.path().join("main.lim"))
                } else {
                    lim::parse_program_from_path_with_config_and_cache(
                        &source,
                        &scratch.path().join("main.lim"),
                        &lim::CompileConfig::default(),
                        &scratch.path().join(".lim/cache"),
                    )
                }
                .and_then(|program| lim::check_types(&program));
                if allowed {
                    result.unwrap_or_else(|error| panic!("{target}, cache mode {mode}: {error}"));
                } else {
                    let error = result
                        .expect_err("a dependency must not become a third privileged context");
                    assert!(
                        error.contains("private"),
                        "{target}, cache mode {mode}: {error}"
                    );
                }
            }
        }
    }
}

#[test]
fn same_physical_caller_under_two_prefixes_does_not_share_private_access() {
    let scratch = support::Scratch::new("generator-context-prefix-matrix");
    write(scratch.path(), "producer/lib.lim", "(#export make) (#gn make (name text) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol text) ())))))");
    write(scratch.path(), "caller/lib.lim", "(#export read) (#import-external \"../producer/lib.lim\" producer) (#fn hidden () #u64 (#return 42u64)) (#generate producer@make read \"one@hidden\")");
    for order in [["one", "two"], ["two", "one"]] {
        let source = format!("(#import-external \"caller/lib.lim\" {}) (#import-external \"caller/lib.lim\" {}) (#fn main () #u64 (#return 0u64))", order[0], order[1]);
        for _ in 0..2 {
            let error = lim::parse_program_from_path_with_config_and_cache(
                &source,
                &scratch.path().join("main.lim"),
                &lim::CompileConfig::default(),
                &scratch.path().join(".lim/cache"),
            )
            .and_then(|program| lim::check_types(&program))
            .expect_err("the second instance cannot use the first instance's private function");
            assert!(
                error.contains("private") && error.contains("one@hidden"),
                "{error}"
            );
        }
    }
}
