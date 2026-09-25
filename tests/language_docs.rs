use std::{fs, path::PathBuf};

#[test]
fn language_reference_code_parses_and_complete_programs_typecheck() {
    let documentation = include_str!("../docs/language.md");
    let mut in_lisp = false;
    let mut block = String::new();
    let mut blocks = Vec::new();
    for line in documentation.lines() {
        if !in_lisp {
            if line.trim() == "```lisp" {
                in_lisp = true;
                block.clear();
            }
        } else if line.trim() == "```" {
            blocks.push(block.clone());
            in_lisp = false;
        } else {
            block.push_str(line);
            block.push('\n');
        }
    }
    assert!(!in_lisp, "unterminated Lim code fence");
    assert!(
        !blocks.is_empty(),
        "no Lim examples found in language reference"
    );

    let directory = std::env::temp_dir().join(format!("lim-language-docs-{}", std::process::id()));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).unwrap();
    let config = lim::CompileConfig::default();
    let mut complete_programs = 0;
    for (index, source) in blocks.iter().enumerate() {
        lim::parse(source).unwrap_or_else(|error| {
            panic!(
                "language reference Lim block {} does not parse: {error}\n{source}",
                index + 1
            )
        });
        if source.contains("(#fn main") {
            complete_programs += 1;
            let path: PathBuf = directory.join(format!("example-{index}.lim"));
            lim::compile_source_to_assembly(
                source,
                &path,
                &config,
                &directory.join(format!("cache-{index}")),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_or_else(|diagnostic| {
                panic!(
                    "complete language reference Lim block {} does not compile: {}\n{source}",
                    index + 1,
                    diagnostic.message
                )
            });
        }
    }
    assert!(complete_programs > 0, "no complete Lim examples found");
    fs::remove_dir_all(directory).unwrap();
}
