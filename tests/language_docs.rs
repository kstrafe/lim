use std::{fs, process::Command};

fn fences(document: &str) -> Vec<(String, String)> {
    let mut result = Vec::new();
    let mut current = None;
    for line in document.lines() {
        if let Some(metadata) = line.strip_prefix("```lisp") {
            assert!(current.is_none());
            assert!(
                !metadata.trim().is_empty(),
                "Lim fences require explicit test metadata"
            );
            current = Some((metadata.trim().to_owned(), String::new()));
        } else if line == "```" {
            if let Some(block) = current.take() {
                result.push(block);
            }
        } else if let Some((_, source)) = &mut current {
            source.push_str(line);
            source.push('\n');
        }
    }
    assert!(current.is_none(), "unterminated Lim fence");
    result
}

#[test]
fn classification_uses_metadata_not_main_spelling() {
    let examples = fences("```lisp library\n; (#fn main is only a comment\n(#type Byte u8)\n```\n```lisp run=42\n(#fn\n main () u64 (#return 42u64))\n```\n");
    assert_eq!(examples[0].0, "library");
    assert_eq!(examples[1].0, "run=42");
}

#[test]
fn documented_programs_compile_and_run() {
    let directory = std::env::temp_dir().join(format!("lim-docs-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let mut config = lim::CompileConfig::default();
    config.set("feature", "fast");
    for (name, document) in [
        ("README", include_str!("../README.md")),
        ("language", include_str!("../docs/language.md")),
        ("allocator", include_str!("../docs/allocator.md")),
        ("soundness", include_str!("../docs/soundness-audit.md")),
    ] {
        for (index, (mode, mut source)) in fences(document).into_iter().enumerate() {
            lim::parse(&source).unwrap_or_else(|error| panic!("{name} fence {index}: {error}"));
            if mode == "syntax" {
                continue;
            }
            if let Some(fragment) = mode.strip_prefix("fragment=") {
                let epilogue = match fragment {
                    "atomics" => "(#forget counter) (#return ())",
                    "array" | "bindings" | "slices" => "(#return ())",
                    _ => panic!("unknown fragment prelude: {fragment}"),
                };
                source = format!("(#fn main () ()\n{source}\n{epilogue})");
            }
            let path = directory.join(format!("{name}-{index}.lim"));
            let result = lim::compile_source_to_assembly(
                &source,
                &path,
                &config,
                &directory.join(format!("cache-{name}-{index}")),
                lim::TargetDescription::X86_64_SYSTEM_V,
            );
            if let Some(code) = mode.strip_prefix("error=") {
                let error = result.unwrap_err();
                assert_eq!(error.code_string(), code);
                assert!(error.span.is_some());
                continue;
            }
            assert!(
                mode == "library" || mode.starts_with("run=") || mode.starts_with("fragment="),
                "unknown metadata: {mode}"
            );
            let assembly = result.unwrap_or_else(|error| {
                panic!(
                    "{name} fence {} ({mode}): {}\n{source}",
                    index + 1,
                    error.message
                )
            });
            if let Some(expected) = mode.strip_prefix("run=") {
                let binary = directory.join(format!("{name}-{index}"));
                lim::link_native_binary(
                    &assembly,
                    &binary,
                    &[],
                    &[],
                    lim::TargetDescription::X86_64_SYSTEM_V,
                )
                .unwrap();
                assert_eq!(
                    Command::new(binary).status().unwrap().code(),
                    Some(expected.parse().unwrap())
                );
            }
        }
    }
    fs::remove_dir_all(directory).unwrap();
}
