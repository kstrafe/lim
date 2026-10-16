//! Graph lowering shares the single-evaluation while-let source semantics.
mod support;

use std::{fs, process::Command, time::Duration};

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("async-graph-while-let");
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let mut previous = None;
    for _ in 0..2 {
        let assembly = lim::compile_source_with_generated_sources(
            source,
            &path,
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &output,
        )
        .unwrap_or_else(|error| panic!("{error:?}"));
        if let Some(previous) = previous.as_ref() {
            assert_eq!(&assembly, previous);
        }
        let artifact = fs::read_dir(&output)
            .unwrap()
            .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
            .find(|text| text.contains("(#fn work-poll "))
            .unwrap();
        let invocation = lim::parse(source)
            .unwrap()
            .into_iter()
            .find(|node| source[node.span.start..node.span.end].starts_with("(@#async-fn"))
            .unwrap();
        let standalone = format!(
            "{}\n{artifact}\n{}",
            &source[..invocation.span.start],
            &source[invocation.span.end..]
        );
        let ordinary = lim::parse_program(&standalone).unwrap();
        lim::check_types(&ordinary).unwrap();
        for (index, native) in [
            assembly.as_str(),
            lim::generate_assembly(&ordinary).unwrap().as_str(),
        ]
        .into_iter()
        .enumerate()
        {
            let binary = scratch.path().join(format!("program-{index}"));
            lim::link_native_binary(
                native,
                &binary,
                &[],
                &[],
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
            let (status, stdout, stderr) =
                support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
            assert_eq!(status.code(), Some(expected), "{stderr:?}");
            assert!(stdout.is_empty() && stderr.is_empty());
        }
        previous = Some(assembly);
    }
}

#[test]
fn awaited_pattern_can_return_after_two_body_suspensions() {
    let source = include_str!("../examples/async_while_let_return.lim");
    run(source, 42);
    run(
        &source.replace("(StepPending (Resume value))", "(StepReady value)"),
        42,
    );
}

#[test]
fn awaited_pattern_payload_preserves_an_external_reference() {
    let source = include_str!("../examples/async_while_let_return.lim")
        .replace(
            "(#enum Choice () ((Chosen #u64) Empty))",
            "(#enum Choice () ((Chosen (#ref #u64)) Empty))",
        )
        .replace("(Start value)))", "(Start (#deref value))))")
        .replace(
            "(#let chosen #u64",
            "(#let owner #u64 37u64) (#let chosen #u64",
        )
        .replace("(Chosen 37u64)", "(Chosen (#borrow owner))");
    run(&source, 42);
}

#[test]
fn awaited_pattern_dependencies_are_evaluated_once_per_iteration() {
    let source = include_str!("../examples/async_while_let_dependencies.lim");
    run(source, 40);
    run(
        &source.replace(
            "(#set choice Empty)",
            "(#block (#set choice Empty) (#continue))",
        ),
        40,
    );
    run(
        &source.replace(
            "(#set choice Empty)",
            "(#block (#set choice Empty) (#break))",
        ),
        39,
    );
}
