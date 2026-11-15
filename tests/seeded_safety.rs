//! Reproducible, bounded fuzz-style corpora; no external fuzzing dependencies.
mod support;
use std::{process::Command, time::Duration};

const SEED: u64 = 0x2026_1028_cafe_51ed;
fn next(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}

#[test]
fn seeded_reader_corpus_never_panics_and_formatting_preserves_syntax() {
    let tokens = [
        "(",
        ")",
        " ",
        "\n",
        ":",
        "@name",
        "#fn",
        "#u64",
        "42u64",
        "`",
        ",",
        ",@",
        "'",
        "\"",
        "\\",
        "λ",
        "//comment\n",
        "#\\newline",
        "$",
        "-",
        "::",
    ];
    let mut state = SEED;
    for case in 0..1024 {
        let length = (next(&mut state) % 48) as usize;
        let source = (0..length)
            .map(|_| tokens[next(&mut state) as usize % tokens.len()])
            .collect::<String>();
        let result = std::panic::catch_unwind(|| {
            if let Ok(tokens) = lim::lex(&source) {
                for token in tokens {
                    assert!(token.span.start <= token.span.end && token.span.end <= source.len());
                    assert!(
                        source.is_char_boundary(token.span.start)
                            && source.is_char_boundary(token.span.end)
                    );
                }
            }
            if let Ok(parsed) = lim::parse(&source) {
                if let Ok(formatted) = lim::format_syntax(&source) {
                    let reparsed =
                        lim::parse(&formatted).expect("formatter must emit readable syntax");
                    assert_eq!(
                        parsed.iter().map(|node| &node.expr).collect::<Vec<_>>(),
                        reparsed.iter().map(|node| &node.expr).collect::<Vec<_>>()
                    );
                    assert_eq!(lim::format_syntax(&formatted).unwrap(), formatted);
                }
            }
        });
        assert!(
            result.is_ok(),
            "seed={SEED:x}, case={case}, source={source:?}"
        );
    }
}

#[test]
fn seeded_projected_borrows_match_a_small_independent_alias_oracle() {
    let scratch = support::Scratch::new("seeded-borrow-oracle");
    for first_mut in [false, true] {
        for second_mut in [false, true] {
            for same_field in [false, true] {
                let suffix = |mutable| if mutable { "-mut" } else { "" };
                let field = if same_field { "left" } else { "right" };
                let source = format!("#struct Record (#linear) ((left #u64) (right #u64))
#fn main () #u64
                      (#let-mut owner Record (#struct-literal Record ((right 25u64) (left 17u64))))
                      (#let first (#ref{} #u64) (#borrow{} (#get owner left)))
                      (#let second (#ref{} #u64) (#borrow{} (#get owner {field})))
                      (#let left #u64 (#deref first)) (#let right #u64 (#deref second))
                      (#drop second) (#drop first) (#forget owner) (#return (#u64::add-wrap left right))\n", suffix(first_mut), suffix(first_mut), suffix(second_mut), suffix(second_mut));
                let result = lim::compile_source_to_assembly(
                    &source,
                    &scratch.path().join("case.lim"),
                    &lim::CompileConfig::default(),
                    &scratch.path().join("cache"),
                    lim::TargetDescription::X86_64_SYSTEM_V,
                );
                let conflict = same_field && (first_mut || second_mut);
                if conflict {
                    let error =
                        result.expect_err("the independent alias oracle predicts a conflict");
                    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
                    let span = error
                        .span
                        .expect("borrow failures require an offending source span");
                    assert!(
                        source[span.start..span.end].starts_with("#borrow"),
                        "{error:?}"
                    );
                } else {
                    assert!(result.is_ok(), "first_mut={first_mut}, second_mut={second_mut}, same={same_field}: {result:?}");
                }
            }
        }
    }
}

#[test]
fn seeded_aggregate_calls_and_enum_branches_match_rust_integer_results() {
    let scratch = support::Scratch::new("seeded-aggregate-native");
    let mut source = String::from("#struct Wide (#linear) ((left #u8) (marker #u128) (right #u64) (count #u16))\n#enum Choice (#linear) ((Choice.Held Wide) (Choice.Other #u64))\n#fn make ((left #u8) (marker #u128) (right #u64) (count #u16)) Wide\n            (#return (#struct-literal Wide ((count count) (right right) (marker marker) (left left))))\n#fn compute ((choose #bool) (owner Wide)) #u64\n            (#let choice Choice (#if choose (#enum-literal Choice.Held owner) (#block (#forget owner) (#enum-literal Choice.Other 7u64))))\n            (#return (#match choice\n              (#case (Choice.Held record) (#block\n                (#let result #u64 (#u64::add-wrap (#u64::add-wrap (#as (#get record left) #u64) (#as (#get record marker) #u64)) (#u64::add-wrap (#get record right) (#as (#get record count) #u64))))\n                (#forget record) result))\n              (#case (Choice.Other value) value)))\n#fn main () #u64\n");
    let mut state = SEED;
    for case in 0..32 {
        let left = next(&mut state) as u8;
        let marker = ((next(&mut state) as u128) << 64) | next(&mut state) as u128;
        let right = next(&mut state);
        let count = next(&mut state) as u16;
        let choose = case % 3 != 0;
        let expected = if choose {
            (left as u64)
                .wrapping_add(marker as u64)
                .wrapping_add(right)
                .wrapping_add(count as u64)
        } else {
            7
        };
        source.push_str(&format!("  (#assert (#u64::eq (#call compute ((owner (#call make ((count {count}u16) (right {right}u64) (marker {marker}u128) (left {left}u8)))) (choose {choose}))) {expected}u64))\n"));
    }
    source.push_str("  (#return 42u64)");
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("case.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("seed={SEED:x}: {error:?}"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "seed={SEED:x}: {stderr:?}");
}

#[test]
#[ignore = "manual end-to-end reference-branch benchmark; run with --ignored --nocapture"]
fn pathological_reference_programs_report_cold_and_warm_check_codegen_times() {
    fn tree(start: usize, end: usize) -> String {
        if end - start == 1 {
            return format!("(#borrow (#index owner {start}usize))");
        }
        let middle = (start + end) / 2;
        format!(
            "(#if (#u64::lt control {middle}u64) {} {})",
            tree(start, middle),
            tree(middle, end)
        )
    }
    let scratch = support::Scratch::new("pathological-reference-programs");
    for width in [8, 32, 128] {
        let source = format!("#fn select ((control #u64) (owner (#ref (#array #u64 {width})))) (#ref #u64) (#return {})\n#fn main () #u64 (#return 42u64)\n", tree(0, width));
        let mut previous = None;
        for pass in 0..3 {
            let start = std::time::Instant::now();
            let assembly = lim::compile_source_to_assembly(
                &source,
                &scratch.path().join("main.lim"),
                &lim::CompileConfig::default(),
                &scratch.path().join(format!("cache-{width}")),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
            println!("reference branch program: width={width}, pass={pass}, cache={}, source_bytes={}, elapsed_ms={:.3}, assembly_bytes={}", if pass == 0 { "cold" } else { "warm" }, source.len(), start.elapsed().as_secs_f64() * 1000.0, assembly.len());
            if let Some(previous) = &previous {
                assert_eq!(previous, &assembly);
            }
            previous = Some(assembly);
        }
    }
}
