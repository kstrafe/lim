mod support;

use std::{fs, path::Path};

fn write_module(root: &Path, name: &str, source: &str) {
    fs::write(root.join(name), source).unwrap();
}

fn materialize(root: &Path, entry: &str, output: &str, cache: &str) -> Vec<String> {
    let source_path = root.join(entry);
    let source = fs::read_to_string(&source_path).unwrap();
    let output = root.join(output);
    let cache = root.join(cache);
    lim::write_generated_sources_from_path_with_config_and_cache(
        &source,
        &source_path,
        &output,
        &lim::CompileConfig::default(),
        &cache,
    )
    .unwrap();
    let sources = fs::read_dir(output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .collect::<Vec<_>>();
    for source in &sources {
        lim::parse_source_unit(source).expect("emitted generated source parses");
    }
    sources
}

fn assert_origins(source: &str, expected: &[String]) {
    let header = source
        .split_once("\n\n")
        .expect("generated file has an origin header")
        .0;
    let actual = header
        .lines()
        .skip(1)
        .map(|line| line.strip_prefix("// ").unwrap().to_owned())
        .collect::<Vec<_>>();
    let mut expected = expected.to_vec();
    expected.sort();
    expected.dedup();
    assert_eq!(actual, expected);
}

fn assert_origin_groups(sources: &[&str], expected: &[Vec<String>]) {
    let mut actual = sources
        .iter()
        .map(|source| {
            let origins = source
                .split_once("\n\n")
                .unwrap()
                .0
                .lines()
                .skip(1)
                .map(|line| line.strip_prefix("// ").unwrap().to_owned())
                .collect::<Vec<_>>();
            assert_origins(source, &origins);
            origins
        })
        .collect::<Vec<_>>();
    let mut expected = expected.to_vec();
    for origins in &mut expected {
        origins.sort();
        origins.dedup();
    }
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected);
}

fn absolute_origin(root: &Path, file: &str, line: usize) -> String {
    format!("{}:{line}", root.join(file).display())
}

#[test]
fn identical_builtin_invocations_deduplicate_within_each_file_and_keep_origins() {
    let scratch = support::Scratch::new("generated-origins-builtin");
    let root = scratch.path();
    write_module(
        root,
        "a.lim",
        "#generate #optional ((type #u64) (name Shared?))\n#generate #optional ((type #u64) (name Shared?))\n",
    );
    write_module(
        root,
        "b.lim",
        "#generate #optional ((type #u64) (name Shared?))\n",
    );
    write_module(
        root,
        "main.lim",
        "#alias FirstValue = ./a.lim::Shared?\n#alias SecondValue = ./b.lim::Shared?\n",
    );

    let generated = materialize(root, "main.lim", "generated", "cache");
    assert!(generated
        .iter()
        .all(|source| source.contains("Shared?::construct")));
    assert_origin_groups(
        &generated.iter().map(String::as_str).collect::<Vec<_>>(),
        &[
            vec![
                absolute_origin(root, "a.lim", 1),
                absolute_origin(root, "a.lim", 2),
            ],
            vec![absolute_origin(root, "b.lim", 1)],
        ],
    );
}

#[test]
fn identical_user_generator_calls_keep_per_file_artifacts_and_origins() {
    let scratch = support::Scratch::new("generated-origins-user");
    let root = scratch.path();
    write_module(
        root,
        "defs.lim",
        "#gn emit-shared () `((#type Shared #u64))\n",
    );
    write_module(
        root,
        "a.lim",
        "#alias emit-shared = ./defs.lim::emit-shared\n#generate emit-shared\n#generate emit-shared\n",
    );
    write_module(
        root,
        "b.lim",
        "#alias emit-shared = ./defs.lim::emit-shared\n#generate emit-shared\n",
    );
    write_module(
        root,
        "main.lim",
        "#alias FirstValue = ./a.lim::Shared\n#alias SecondValue = ./b.lim::Shared\n",
    );

    let generated = materialize(root, "main.lim", "generated", "cache");
    assert!(generated
        .iter()
        .all(|source| source.contains("#type Shared #u64")));
    assert_origin_groups(
        &generated.iter().map(String::as_str).collect::<Vec<_>>(),
        &[
            vec![
                absolute_origin(root, "a.lim", 2),
                absolute_origin(root, "a.lim", 3),
            ],
            vec![absolute_origin(root, "b.lim", 2)],
        ],
    );
}

#[test]
fn user_generator_artifacts_are_per_invocation_cache_payloads() {
    let scratch = support::Scratch::new("generated-invocation-payloads");
    let root = scratch.path();
    write_module(
        root,
        "defs.lim",
        "#gn child (name) `((#type ,name #u64))\n#gn parent (name) `((#generate child ,name))\n",
    );
    write_module(
        root,
        "a.lim",
        "#alias parent = ./defs.lim::parent\n#alias child = ./defs.lim::child\n#generate parent First\n#generate child Second\n",
    );
    write_module(
        root,
        "b.lim",
        "#alias parent = ./defs.lim::parent\n#generate parent First\n",
    );
    write_module(
        root,
        "main.lim",
        "#alias FirstValue = ./a.lim::First\n#alias SecondValue = ./b.lim::First\n",
    );
    let mut cold = materialize(root, "main.lim", "generated", "cache");
    assert_eq!(
        cold.len(),
        5,
        "each file has its own parent/child payloads, plus the second child in a.lim"
    );
    for marker in ["#type First #u64\n", "#generate", "#type Second #u64\n"] {
        let matching = cold
            .iter()
            .filter(|source| {
                if marker == "#generate" {
                    lim::parse_source_unit(source).unwrap().iter().any(|node| {
                        matches!(&node.expr, lim::Expr::List(items)
                            if matches!(items.first(), Some(lim::Expr::Generate)))
                    })
                } else {
                    source.contains(marker)
                }
            })
            .map(String::as_str)
            .collect::<Vec<_>>();
        let expected = if marker == "#type Second #u64\n" {
            vec![vec![absolute_origin(root, "a.lim", 4)]]
        } else {
            vec![
                vec![absolute_origin(root, "a.lim", 3)],
                vec![absolute_origin(root, "b.lim", 2)],
            ]
        };
        assert_origin_groups(&matching, &expected);
    }
    assert!(fs::read_dir(root.join("cache")).unwrap().all(|entry| entry
        .unwrap()
        .path()
        .extension()
        .is_some_and(|extension| extension == "key")));
    let paths = fs::read_dir(root.join("generated"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    let modified = paths
        .iter()
        .map(|path| fs::metadata(path).unwrap().modified().unwrap())
        .collect::<Vec<_>>();
    let mut warm = materialize(root, "main.lim", "generated", "cache");
    cold.sort();
    warm.sort();
    assert_eq!(cold, warm);
    assert_eq!(
        modified,
        paths
            .iter()
            .map(|path| fs::metadata(path).unwrap().modified().unwrap())
            .collect::<Vec<_>>()
    );
    let child = paths
        .iter()
        .find(|path| {
            fs::read_to_string(path)
                .unwrap()
                .contains("#type First #u64")
        })
        .unwrap();
    fs::write(child, "#type Corrupted #u64\n").unwrap();
    let mut repaired = materialize(root, "main.lim", "generated", "cache");
    repaired.sort();
    assert_eq!(
        repaired, cold,
        "the actual compilation payload is integrity checked and regenerated"
    );
}

#[test]
fn inspectable_user_generator_output_cannot_be_silently_discarded() {
    let scratch = support::Scratch::new("generated-unwritable-cache");
    let root = scratch.path();
    let cache = root.join("cache");
    fs::write(&cache, "this is a file, not a cache directory").unwrap();
    let result = lim::write_generated_sources_from_path_with_config_and_cache(
        "#gn emit () `((#type Value #u64))\n#generate emit\n",
        &root.join("main.lim"),
        &root.join("generated"),
        &lim::CompileConfig::default(),
        &cache,
    );
    assert!(
        result.is_err(),
        "an unavailable source artifact must fail materialization"
    );
}

#[test]
fn duplicate_invocations_load_once_and_publish_all_origins_once() {
    let scratch = support::Scratch::new("generator-ram-lookup");
    let root = scratch.path();
    let input = root.join("main.lim");
    let cache = root.join("cache");
    let source = format!(
        "#gn child () `((#type Shared #u64))\n#gn parent () `((#generate child))\n{}",
        "#generate parent\n".repeat(64)
    );
    let run = |source: &str| {
        lim::with_cache_report(|| {
            lim::write_generated_sources_from_path_with_config_and_cache(
                source,
                &input,
                &root.join("generated"),
                &lim::CompileConfig::default(),
                &cache,
            )
            .unwrap();
        })
        .1
    };
    let cold = run(&source);
    assert_eq!(
        cold.matches("\"kind\":\"syntax-publication\"").count(),
        2,
        "publish parent and child once, not once per caller"
    );
    assert_eq!(cold.matches("\"kind\":\"syntax-read\"").count(), 0);
    let warm = run(&source);
    assert_eq!(
        warm.matches("\"kind\":\"syntax-read\"").count(),
        2,
        "read parent and child once, not once per caller"
    );
    assert_eq!(warm.matches("\"kind\":\"syntax-publication\"").count(), 0);
    let expected = (3..67)
        .map(|line| format!("{}:{line}", input.display()))
        .collect::<Vec<_>>();
    for entry in fs::read_dir(root.join("generated")).unwrap() {
        assert_origins(
            &fs::read_to_string(entry.unwrap().path()).unwrap(),
            &expected,
        );
    }
    // A separate compilation must revalidate changed source/dependencies.
    let changed = run(&source.replace("#u64", "#u32"));
    assert_eq!(
        changed.matches("\"kind\":\"syntax-publication\"").count(),
        2
    );
    assert_eq!(changed.matches("\"kind\":\"syntax-read\"").count(), 0);
}

#[test]
fn repeated_builtin_materialization_uses_one_cache_lookup() {
    let scratch = support::Scratch::new("builtin-ram-lookup");
    let root = scratch.path();
    let input = root.join("main.lim");
    let source = "#generate #optional ((type #u64) (name Shared))\n".repeat(64);
    let run = || {
        lim::with_cache_report(|| {
            lim::write_generated_sources_from_path_with_config_and_cache(
                &source,
                &input,
                &root.join("generated"),
                &lim::CompileConfig::default(),
                &root.join("cache"),
            )
            .unwrap()
        })
        .1
    };
    assert_eq!(run().matches("\"kind\":\"source\"").count(), 1);
    assert_eq!(run().matches("\"kind\":\"source\"").count(), 1);
    let expected = (1..65)
        .map(|line| format!("{}:{line}", input.display()))
        .collect::<Vec<_>>();
    for entry in fs::read_dir(root.join("generated")).unwrap() {
        assert_origins(
            &fs::read_to_string(entry.unwrap().path()).unwrap(),
            &expected,
        );
    }
}

#[test]
fn nested_generator_builtin_origins_include_both_source_invocations() {
    let scratch = support::Scratch::new("generated-origins-nested");
    let root = scratch.path();
    // Each file owns a fresh generated type, including through nested cache hits.
    write_module(
        root,
        "defs.lim",
        "#gn wrap-shared () `((#generate #optional ((type #u64) (name ,(#gn-gensym \"Nested\")))))\n",
    );
    write_module(
        root,
        "a.lim",
        "#alias wrap-shared = ./defs.lim::wrap-shared\n#generate wrap-shared\n#generate wrap-shared\n",
    );
    write_module(
        root,
        "b.lim",
        "#alias wrap-shared = ./defs.lim::wrap-shared\n#generate wrap-shared\n",
    );
    write_module(
        root,
        "main.lim",
        "#alias first-generator = ./a.lim::wrap-shared\n#alias second-generator = ./b.lim::wrap-shared\n",
    );

    let cold = materialize(root, "main.lim", "generated", "cache");
    let warm = materialize(root, "main.lim", "generated", "cache");
    assert_eq!(cold, warm);
    assert_eq!(
        warm.len(),
        4,
        "each file emits invocation and builtin artifacts"
    );
    let origins = [
        vec![
            absolute_origin(root, "a.lim", 2),
            absolute_origin(root, "a.lim", 3),
        ],
        vec![absolute_origin(root, "b.lim", 2)],
    ];
    for builtin in [true, false] {
        let artifacts = warm
            .iter()
            .filter(|source| source.contains("Nested::construct") == builtin)
            .map(String::as_str)
            .collect::<Vec<_>>();
        assert_origin_groups(&artifacts, &origins);
    }
}

#[test]
fn warm_generation_retains_per_file_artifacts_and_origins() {
    let scratch = support::Scratch::new("generated-origins-warm");
    let root = scratch.path();
    write_module(
        root,
        "a.lim",
        "#generate #optional ((type #u64) (name Warm?))\n",
    );
    write_module(
        root,
        "b.lim",
        "#generate #optional ((type #u64) (name Warm?))\n",
    );
    write_module(
        root,
        "main.lim",
        "#alias FirstValue = ./a.lim::Warm?\n#alias SecondValue = ./b.lim::Warm?\n",
    );

    let cold = materialize(root, "main.lim", "generated", "cache");
    let warm = materialize(root, "main.lim", "generated", "cache");
    assert_eq!(cold, warm);
    assert_origin_groups(
        &warm.iter().map(String::as_str).collect::<Vec<_>>(),
        &[
            vec![absolute_origin(root, "a.lim", 1)],
            vec![absolute_origin(root, "b.lim", 1)],
        ],
    );
}

#[test]
fn async_short_await_protocol_is_preserved_in_annotated_generated_source() {
    let scratch = support::Scratch::new("generated-origins-async");
    let root = scratch.path();
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/async_fn.lim");
    let source = fs::read_to_string(&example).unwrap();
    let invocation_line = lim::parse_source_unit(&source)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.first(), Some(lim::Expr::Generate))
                && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == "#async-fn"))
        })
        .expect("example contains an async generator invocation")
        .span
        .line;
    let output = root.join("generated");
    lim::write_generated_sources_from_path_with_config_and_cache(
        &source,
        &example,
        &output,
        &lim::CompileConfig::default(),
        &root.join("cache"),
    )
    .unwrap();
    let has_work_protocol = |source: &str| {
        lim::parse_source_unit(source).unwrap().iter().any(|node| {
            matches!(&node.expr, lim::Expr::List(items)
                if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#syntax")
                    && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name.ends_with(".lim::WorkAwait")))
        })
    };
    let generated = fs::read_dir(output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|source| has_work_protocol(source))
        .expect("async protocol source was materialized");
    lim::parse_source_unit(&generated).expect("async generated source parses");
    assert!(generated.starts_with("// Generated from:\n// "));
    assert!(!generated.contains("#await"), "{generated}");
    assert!(has_work_protocol(&generated), "{generated}");
    assert!(generated.contains("Work::poll"), "{generated}");
    assert!(generated.contains("Work::Poll"), "{generated}");
    assert_origins(
        &generated,
        &[absolute_origin(
            example.parent().unwrap(),
            "async_fn.lim",
            invocation_line,
        )],
    );
}
