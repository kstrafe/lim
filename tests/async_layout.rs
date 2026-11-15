#[path = "support/generated_source.rs"]
mod generated_source;
mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn forward_child_layouts_use_untagged_parent_storage_on_cold_and_warm_runs() {
    let source = include_str!("../examples/async_composition.lim");
    let scratch = support::Scratch::new("async-child-layouts");
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let artifacts = scratch.path().join("generated");
    let config = lim::CompileConfig::default();
    for iteration in 0..2 {
        let assembly = lim::compile_source_to_assembly(
            source,
            &path,
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{error:?}"));
        let binary = scratch.path().join(format!("program-{iteration}"));
        lim::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let (status, _, _) =
            support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
        assert_eq!(status.code(), Some(42));
        lim::write_generated_sources_from_path_with_config_and_cache(
            source, &path, &artifacts, &config, &cache,
        )
        .unwrap();
    }
    let generated = fs::read_dir(&artifacts)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .collect::<Vec<_>>();
    let parent = generated
        .iter()
        .find(|source| source.contains("#fn Parent::poll "))
        .unwrap();
    assert!(
        parent.contains("(#array Child::Task 0)"),
        "child must have untagged owning storage"
    );
    // Both inspectable artifacts must also work without generator metadata.
    let forms = lim::parse_source_unit(source).unwrap();
    let mut standalone = String::new();
    let mut cursor = 0;
    for form in forms {
        if source[form.span.start..form.span.end].starts_with("#generate #async-fn") {
            standalone.push_str(&source[cursor..form.span.start]);
            cursor = form.span.end;
        }
    }
    standalone.push_str(&source[cursor..]);
    for artifact in generated {
        standalone.push_str(&generated_source::ordinary_source(&artifact));
    }
    let program = lim::parse_program(&standalone).unwrap();
    let fields = program
        .items
        .iter()
        .find_map(|item| match item {
            lim::Item::Struct { name, fields, .. } if name == "Parent::Task" => Some(fields),
            _ => None,
        })
        .unwrap();
    for field in fields {
        if let lim::Type::Named(name) = &field.ty {
            let tagged_child = program.items.iter().any(|item| matches!(item,
                lim::Item::Enum {name: cell, variants, ..} if cell == name
                    && variants.iter().any(|variant| variant.fields == [lim::Type::Named("Child::Task".into())])
            ));
            assert!(
                !tagged_child,
                "parent child field still has an occupancy tag"
            );
        }
    }
    lim::check_types(&program).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("standalone");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096)
            .unwrap()
            .0
            .code(),
        Some(42)
    );
}
