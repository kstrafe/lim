mod support;

use std::fs;

#[test]
fn direct_nested_and_repeated_builtin_calls_share_one_checked_artifact() {
    for (generator, builtin) in [
        (
            "#optional",
            "(#generate #optional (: type #u64 : name Shared))",
        ),
        (
            "#array",
            "(#generate #array (: element #u64 : length 4 : name Shared))",
        ),
    ] {
        for invocations in [
            format!("(#generate outer)\n{builtin}\n{builtin}"),
            format!("{builtin}\n(#generate outer)\n{builtin}"),
        ] {
            let scratch = support::Scratch::new("builtin-generator-dedup");
            let entry = scratch.path().join("main.lim");
            let source = format!(
                "(#gn outer () `({builtin}))\n{invocations}\n(#fn main () #u64 (#return 0u64))"
            );
            for _ in 0..2 {
                let outer = source.rfind("(#generate outer)").unwrap();
                let direct = source.rfind(builtin).unwrap();
                let nested = lim::locate_generated_details(
                    &source,
                    &entry,
                    &lim::CompileConfig::default(),
                    &entry,
                    outer,
                    outer,
                )
                .unwrap();
                assert_eq!(nested.len(), 2, "{nested:?}");
                assert_eq!(nested[0].generator, "outer");
                let artifact = nested
                    .iter()
                    .find(|artifact| artifact.generator == generator)
                    .unwrap();
                assert!(artifact.nested);
                let direct = lim::locate_generated_details(
                    &source,
                    &entry,
                    &lim::CompileConfig::default(),
                    &entry,
                    direct,
                    direct,
                )
                .unwrap();
                assert_eq!(direct.len(), 1);
                assert!(!direct[0].nested);
                assert_eq!(direct[0].path, artifact.path);
                let text = fs::read_to_string(&artifact.path).unwrap();
                for line in source.lines().enumerate().filter_map(|(index, line)| {
                    (line == builtin || line == "(#generate outer)").then_some(index + 1)
                }) {
                    assert!(
                        text.contains(&format!("{}:{line}", entry.display())),
                        "{text}"
                    );
                }
                assert_eq!(
                    fs::read_dir(scratch.path().join(".lim/generated"))
                        .unwrap()
                        .count(),
                    2
                );
            }
        }
    }
}

#[test]
fn canonical_named_argument_order_deduplicates_but_different_inputs_do_not() {
    let scratch = support::Scratch::new("builtin-canonical-dedup");
    let entry = scratch.path().join("main.lim");
    for source in [
        "(#generate #optional (: type #u64 : name Shared)) (#generate #optional (: name Shared : type #u64))",
        "(#generate #array (: element #u64 : length 4 : name Shared)) (#generate #array (: name Shared : length 4 : element #u64)) (#require-generated Shared #array (Shared::get Shared::borrow Shared::borrow-mut))",
        "(#gn outer () `((#generate #optional (: name Shared : type #u64)))) (#generate outer) (#generate #optional (: type #u64 : name Shared)) (#require-generated Shared outer (Shared::construct)) (#require-generated Shared #optional (Shared::construct))",
    ] {
        lim::check_source_with_generated_sources(source, &entry, &lim::CompileConfig::default(), &scratch.path().join("cache"), &scratch.path().join("generated")).unwrap();
    }
    let invalid =
        "(#generate #optional (: type #u64 : name Shared)) (#generate #optional (: type #u32 : name Shared))";
    let error = lim::check_source_with_generated_sources(
        invalid,
        &entry,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        &scratch.path().join("generated"),
    )
    .unwrap_err();
    assert!(error.message.contains("duplicate"), "{error:?}");
}
