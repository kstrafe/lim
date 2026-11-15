use std::{fs, process::Command};

#[test]
fn homepage_introduces_lim_before_the_tutorial_and_full_reference() {
    let homepage = include_str!("../docs/index.html");
    let sections = [
        "introduction",
        "tutorial",
        "language-reference",
        "verification-notes",
        "browser-compiler",
    ];
    let positions: Vec<_> = sections
        .iter()
        .map(|id| {
            homepage
                .find(&format!("id=\"{id}\""))
                .unwrap_or_else(|| panic!("missing section {id}"))
        })
        .collect();
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));
    for id in [
        "language",
        "safety",
        "start",
        "contracts-tutorial",
        "fixed-array-apis",
        "browser-abi",
    ] {
        assert!(
            homepage.contains(&format!("id=\"{id}\"")),
            "missing handbook navigation anchor {id}"
        );
    }
    assert!(!homepage.contains("<script"));
    assert!(!homepage.contains("<details"));
}

#[test]
fn builtin_reference_is_sorted_and_covers_parser_forms() {
    assert!(
        include_str!("../src/lib.rs").contains("#![doc = include_str!(\"../docs/language.md\")]"),
        "the language reference must also be the crate-level documentation"
    );
    let reference = include_str!("../docs/language.md")
        .split("### Complete `#` builtin reference (alphabetical)")
        .nth(1)
        .expect("builtin reference heading")
        .split("#### Typed operator families")
        .next()
        .unwrap();
    let documented: Vec<&str> = reference
        .lines()
        .filter_map(|line| {
            let cells: Vec<&str> = line.split('|').map(str::trim).collect();
            let name = cells.get(1)?.strip_prefix('`')?.strip_suffix('`')?;
            assert_eq!(cells.len(), 6, "{name}: expected four populated columns");
            assert!(
                cells[2..5].iter().all(|cell| !cell.is_empty()),
                "{name}: empty reference cell"
            );
            assert!(
                cells[3].contains(" (`") || cells[3].contains(" ("),
                "{name}: example needs a context label"
            );
            let delimiter = if cells[3].starts_with("``") {
                "``"
            } else {
                "`"
            };
            let example = cells[3]
                .strip_prefix(delimiter)
                .unwrap()
                .split(delimiter)
                .next()
                .unwrap();
            let parsed = if cells[3].contains("(top level)")
                || cells[3].contains("(compiler-generated file header)")
            {
                lim::parse_source_unit(example)
            } else {
                lim::parse(example)
            };
            parsed.unwrap_or_else(|error| panic!("{name}: invalid example syntax: {error}"));
            assert!(
                example.contains(name),
                "{name}: contextual example must demonstrate this builtin"
            );
            Some(name)
        })
        .collect();
    assert!(
        documented.windows(2).all(|pair| pair[0] < pair[1]),
        "builtin reference must be sorted and unique"
    );

    let compiler = include_str!("../src/lib.rs");
    let registry = compiler
        .split("fn is_builtin_form(name: &str) -> bool {")
        .nth(1)
        .expect("builtin form registry")
        .split("fn is_operator_symbol")
        .next()
        .unwrap();
    for token in registry.split('"').skip(1).step_by(2) {
        assert!(
            documented.contains(&format!("#{token}").as_str()),
            "missing compiler builtin #{token} from crate-level docs"
        );
    }
    // These forms are dispatched in specialized parser paths, outside the
    // legacy is_builtin_form registry.
    for name in [
        "#array-of",
        "#gn-length",
        "#let-mut",
        "#struct-literal",
        "#syntax",
        "#distributed-enum",
        "#enum-contribute",
        "#syntax-splice",
        "#abi-c",
        "#arch",
        "#os",
        "#platform",
        "#pin-read",
        "#pin-set-field",
        "#pin-write",
        "#repr-c",
        "#send",
        "#sync",
        "#target",
        "#body",
        "#params",
        "#returns",
        "#saturate",
        "#value",
        "#wrap",
    ] {
        assert!(
            documented.contains(&name),
            "missing specialized builtin {name}"
        );
    }

    // Interpreter dispatch is separate from the runtime parser registry.
    let generator = include_str!("../src/generator.rs");
    for token in generator.split('"').skip(1).step_by(2) {
        if token.starts_with("#gn-")
            && token.len() > "#gn-".len()
            && token
                .chars()
                .all(|c| c.is_ascii_lowercase() || "#-?".contains(c))
        {
            assert!(
                documented.contains(&token),
                "undocumented generator builtin {token}"
            );
        }
    }
}

#[test]
fn generator_reference_documents_iteration_shadowing() {
    let reference = include_str!("../docs/language.md");
    assert!(
        reference.contains("`#gn-for-each` binding cannot shadow a generator parameter"),
        "the generator reference must describe the no-shadowing rule"
    );
    assert!(
        reference.contains("sibling iteration forms have independent scopes"),
        "the generator reference must clarify sibling binding scopes"
    );
}

#[test]
fn operator_reference_examples_typecheck() {
    let reference = include_str!("../docs/language.md")
        .split("#### Typed operator families (alphabetical)")
        .nth(1)
        .unwrap()
        .split("### Conditionals and blocks")
        .next()
        .unwrap();
    let mut previous = String::new();
    for row in reference.lines().filter(|line| line.starts_with("| `#")) {
        // Split column separators, not escaped pipe operators in code spans.
        let cells: Vec<_> = row.split(" | ").collect();
        assert_eq!(cells.len(), 4, "{row}");
        let name = cells[0]
            .trim_start_matches("| ")
            .trim_matches('`')
            .replace("\\|", "|");
        assert!(name > previous, "operator families must be sorted: {name}");
        previous = name.clone();
        let example = cells[2].split('`').nth(1).unwrap().replace("\\|", "|");
        let source = format!("#fn example () () (#drop {example}) (#return ())");
        let program =
            lim::parse_program(&source).unwrap_or_else(|error| panic!("{name}: {error}\n{source}"));
        lim::check_types(&program).unwrap_or_else(|error| panic!("{name}: {error}\n{source}"));

        // A working u64 example alone does not establish that a family is
        // supported for every advertised qualifier (notably i128 and floats).
        let integers = [
            "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
        ];
        let (family, operation) = name.strip_prefix('#').unwrap().split_once("::").unwrap();
        let qualifiers: Vec<&str> = match family {
            "I" => integers.to_vec(),
            "F" => vec!["f32", "f64"],
            "T" => integers
                .into_iter()
                .chain(["f32", "f64", "bool", "char"])
                .collect(),
            concrete => vec![concrete],
        };
        for qualifier in qualifiers {
            let operand = match qualifier {
                "bool" => "true".to_owned(),
                "char" => "#\\a".to_owned(),
                "f32" | "f64" => format!("1.0{qualifier}"),
                _ => format!("1{qualifier}"),
            };
            let arities: &[usize] = if operation == "not" {
                &[1]
            } else if operation == "sub" || operation.starts_with("sub-") {
                &[1, 2]
            } else {
                &[2]
            };
            for &arity in arities {
                let operands = vec![operand.as_str(); arity].join(" ");
                let source = format!(
                    "#fn example () () (#drop (#{qualifier}::{operation} {operands})) (#return ())"
                );
                let program =
                    lim::parse_program(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
                lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
            }
        }
    }
}

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
    let examples = fences("```lisp library\n// (#fn main is only a comment\n(#type Byte #u8)\n```\n```lisp run=42\n(#fn\n main () #u64 (#return 42u64))\n```\n");
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
        ("tutorial", include_str!("../docs/tutorial.md")),
        ("introduction", include_str!("../docs/introduction.md")),
        ("allocator", include_str!("../docs/allocator.md")),
        ("soundness", include_str!("../docs/soundness-audit.md")),
    ] {
        for (index, (mode, mut source)) in fences(document).into_iter().enumerate() {
            if mode == "syntax" {
                lim::parse(&source)
                    .unwrap_or_else(|error| panic!("{name} syntax fence {index}: {error}"));
                continue;
            }
            if let Some(fragment) = mode.strip_prefix("fragment=") {
                let epilogue = match fragment {
                    "atomics" => "(#forget counter) (#return ())",
                    "array" | "bindings" | "slices" => "(#return ())",
                    _ => panic!("unknown fragment prelude: {fragment}"),
                };
                source = format!(
                    "#fn main () ()\n{}\n  {epilogue}",
                    source
                        .lines()
                        .map(|line| format!("  {line}"))
                        .collect::<Vec<_>>()
                        .join("\n")
                );
            }
            source = source.replace(
                "../library/",
                &format!("{}/library/", env!("CARGO_MANIFEST_DIR")),
            );
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
