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
        lim::parse(source).expect("emitted generated source parses");
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
        .map(|line| line.strip_prefix("; ").unwrap().to_owned())
        .collect::<Vec<_>>();
    let mut expected = expected.to_vec();
    expected.sort();
    expected.dedup();
    assert_eq!(actual, expected);
}

fn absolute_origin(root: &Path, file: &str, line: usize) -> String {
    format!("{}:{line}", root.join(file).display())
}

#[test]
fn identical_builtin_invocations_from_imports_share_an_artifact_and_keep_both_origins() {
    let scratch = support::Scratch::new("generated-origins-builtin");
    let root = scratch.path();
    write_module(root, "a.lim", "(@#optional (: type #u64 : name Shared?))\n");
    write_module(root, "b.lim", "(@#optional (: type #u64 : name Shared?))\n");
    write_module(
        root,
        "main.lim",
        "(#import \"a.lim\")\n(#import \"b.lim\")\n",
    );

    let generated = materialize(root, "main.lim", "generated", "cache");
    let artifact = generated
        .iter()
        .find(|source| source.contains("Shared?-construct"))
        .expect("optional expansion was materialized");
    assert_eq!(
        generated.len(),
        1,
        "identical expansions share one artifact"
    );
    assert_origins(
        artifact,
        &[
            absolute_origin(root, "a.lim", 1),
            absolute_origin(root, "b.lim", 1),
        ],
    );
}

#[test]
fn identical_user_generator_calls_from_imports_keep_both_origins() {
    let scratch = support::Scratch::new("generated-origins-user");
    let root = scratch.path();
    write_module(
        root,
        "defs.lim",
        "(#gn emit-shared () `((#type Shared #u64)))\n",
    );
    write_module(root, "a.lim", "(#import \"defs.lim\")\n(@emit-shared)\n");
    write_module(root, "b.lim", "(#import \"defs.lim\")\n(@emit-shared)\n");
    write_module(
        root,
        "main.lim",
        "(#import \"a.lim\")\n(#import \"b.lim\")\n",
    );

    let generated = materialize(root, "main.lim", "generated", "cache");
    let artifact = generated
        .iter()
        .find(|source| source.contains("(#type Shared #u64)"))
        .expect("user generator output was materialized");
    assert_eq!(
        generated.len(),
        1,
        "identical expansions share one artifact"
    );
    assert_origins(
        artifact,
        &[
            absolute_origin(root, "a.lim", 2),
            absolute_origin(root, "b.lim", 2),
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
        "(#gn child (name) `((#type ,name #u64)))\n(#gn parent (name) `((@child ,name)))\n",
    );
    write_module(
        root,
        "a.lim",
        "(#import \"defs.lim\")\n(@parent First)\n(@child Second)\n",
    );
    write_module(root, "b.lim", "(#import \"defs.lim\")\n(@parent First)\n");
    write_module(
        root,
        "main.lim",
        "(#import \"a.lim\")\n(#import \"b.lim\")\n",
    );
    let mut cold = materialize(root, "main.lim", "generated", "cache");
    assert_eq!(
        cold.len(),
        3,
        "parent and two child invocations have separate payloads"
    );
    for source in &cold {
        if source.contains("First") {
            assert_origins(
                source,
                &[
                    absolute_origin(root, "a.lim", 2),
                    absolute_origin(root, "b.lim", 2),
                ],
            );
        }
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
                .contains("(#type First #u64)")
        })
        .unwrap();
    fs::write(child, "(#type Corrupted #u64)").unwrap();
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
        "(#gn emit () `((#type Value #u64))) (@emit)",
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
        "(#gn child () `((#type Shared #u64)))\n(#gn parent () `((@child)))\n{}",
        "(@parent)\n".repeat(64)
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
    let source = "(@#optional (: type #u64 : name Shared))\n".repeat(64);
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
    write_module(
        root,
        "defs.lim",
        "(#gn wrap-shared () `((@#optional (: type #u64 : name Nested?))))\n",
    );
    write_module(root, "a.lim", "(#import \"defs.lim\")\n(@wrap-shared)\n");
    write_module(root, "b.lim", "(#import \"defs.lim\")\n(@wrap-shared)\n");
    write_module(
        root,
        "main.lim",
        "(#import \"a.lim\")\n(#import \"b.lim\")\n",
    );

    let cold = materialize(root, "main.lim", "generated", "cache");
    let warm = materialize(root, "main.lim", "generated", "cache");
    assert_eq!(cold, warm);
    assert_eq!(
        warm.len(),
        2,
        "nested generation emits invocation and builtin artifacts"
    );
    let origins = [
        absolute_origin(root, "a.lim", 2),
        absolute_origin(root, "b.lim", 2),
    ];
    let artifact = warm
        .iter()
        .find(|source| source.contains("Nested?-construct"))
        .expect("nested optional expansion was materialized");
    assert_origins(artifact, &origins);
    let invocation = warm
        .iter()
        .find(|source| source.contains("(@ #optional") && !source.contains("Nested?-construct"))
        .expect("nested user-generator invocation was materialized");
    assert_origins(invocation, &origins);
}

#[test]
fn warm_generation_retains_one_artifact_and_its_deduplicated_origins() {
    let scratch = support::Scratch::new("generated-origins-warm");
    let root = scratch.path();
    write_module(root, "a.lim", "(@#optional (: type #u64 : name Warm?))\n");
    write_module(root, "b.lim", "(@#optional (: type #u64 : name Warm?))\n");
    write_module(
        root,
        "main.lim",
        "(#import \"a.lim\")\n(#import \"b.lim\")\n",
    );

    let cold = materialize(root, "main.lim", "generated", "cache");
    let warm = materialize(root, "main.lim", "generated", "cache");
    assert_eq!(cold, warm);
    assert_eq!(warm.len(), 1);
    assert_origins(
        &warm[0],
        &[
            absolute_origin(root, "a.lim", 1),
            absolute_origin(root, "b.lim", 1),
        ],
    );
}

#[test]
fn async_short_await_protocol_is_preserved_in_annotated_generated_source() {
    let scratch = support::Scratch::new("generated-origins-async");
    let root = scratch.path();
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/async_fn.lim");
    let source = fs::read_to_string(&example).unwrap();
    let output = root.join("generated");
    lim::write_generated_sources_from_path_with_config_and_cache(
        &source,
        &example,
        &output,
        &lim::CompileConfig::default(),
        &root.join("cache"),
    )
    .unwrap();
    let generated = fs::read_dir(output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|source| source.contains("(#syntax WorkAwait"))
        .expect("async protocol source was materialized");
    lim::parse(&generated).expect("async generated source parses");
    assert!(generated.starts_with("; Generated from:\n; "));
    assert!(!generated.contains("#await"), "{generated}");
    assert!(generated.contains("(#syntax WorkAwait"), "{generated}");
    assert!(generated.contains("Work::poll"), "{generated}");
    assert!(generated.contains("Work::Poll"), "{generated}");
    assert_origins(
        &generated,
        &[absolute_origin(
            example.parent().unwrap(),
            "async_fn.lim",
            49,
        )],
    );
}
