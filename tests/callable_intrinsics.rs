mod support;

use std::{process::Command, time::Duration};

fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

fn execute(source: &str, checks: bool) -> i32 {
    let scratch = support::Scratch::new("callable-intrinsic");
    let mut config = lim::CompileConfig::default();
    if checks {
        config.set("contracts", "check");
    }
    let asm = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &asm,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, error) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    status
        .code()
        .unwrap_or_else(|| panic!("{status}: {}", String::from_utf8_lossy(&error)))
}

#[test]
fn scalar_intrinsics_have_normal_named_calls_and_typed_results() {
    let source = r#"#fn main () #u64
        (#let left #u64 20u64)
        (#let right #u64 22u64)
        (#let sum #u64 (#call #u64::add-wrap (($ right) ($ left))))
        (#assert (#call #u64::eq ((right 42u64) (left sum))))
        (#assert (#call #bool::not ((value false))))
        (#assert (#call #u8::eq ((left (#call #u8::not ((value 255u8)))) (right 0u8))))
        (#assert (#call #i128::lt ((left -2i128) (right 1i128))))
        (#assert (#call #f64::eq ((left (#call #f64::mul ((left 3.0f64) (right 2.0f64)))) (right 6.0f64))))
        (#return sum)
"#;
    assert_eq!(execute(source, false), 42);
}

#[test]
fn intrinsic_arguments_execute_once_in_written_order() {
    let source = r#"#fn next ((counter (#ref-mut #u64)) (expected #u64)) #u64
        (#assert (#u64::eq (#deref counter) expected))
        (#deref-set counter (#u64::add-wrap expected 1u64))
        (#return (#u64::add-wrap 20u64 (#u64::mul-wrap expected 2u64)))
#fn main () #u64
          (#let-mut counter #u64 0u64)
          (#let result #u64 (#call #u64::add-wrap
            ((right (#call next ((counter (#borrow-mut counter)) (expected 0u64))))
             (left (#call next ((counter (#borrow-mut counter)) (expected 1u64)))))))
          (#assert (#u64::eq counter 2u64)) (#return result)
"#;
    assert_eq!(execute(source, false), 42);
}

#[test]
fn array_get_can_return_copy_aggregates() {
    let source = r#"#struct Row () ((a #u64) (b #u64) (c #u64) (d #u64) (e #u64) (f #u64) (g #u64) (h #u64))
#generate #array ((element Row) (length 1) (name Rows))
#fn main () #u64
          (#let values Rows (#array-of (#struct-literal Row ((a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7) (h 42)))))
          (#let index #usize 0usize) (#assume (#call #usize::lt ((left index) (right 1usize))))
          (#let row Row (#call Rows::get ((values (#borrow values)) (index index))))
          (#return (#get row h))
"#;
    for checks in [false, true] {
        assert_eq!(execute(source, checks), 42);
    }
}

#[test]
fn generated_array_artifacts_and_provenance_survive_cache_hits() {
    let scratch = support::Scratch::new("array-api-artifact");
    let entry = scratch.path().join("main.lim");
    let source = "#generate #array ((length 4) (name Array4) (element #u64))\n#require-generated Array4 #array (Array4::get Array4::borrow Array4::prove-in-bounds)\n";
    for _ in 0..2 {
        lim::check_source_with_generated_sources(
            source,
            &entry,
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            &scratch.path().join("generated"),
        )
        .unwrap();
        let artifacts = lim::locate_generated_details(
            source,
            &entry,
            &lim::CompileConfig::default(),
            &entry,
            0,
            0,
        )
        .unwrap();
        assert_eq!(artifacts.len(), 1);
        let text = std::fs::read_to_string(&artifacts[0].path).unwrap();
        assert!(text.contains("Array4::get"));
        assert!(text.contains("#requires"));
        assert!(text.contains("#call #usize::lt"));
        assert!(text.contains("#index-proven"));
    }
}

#[test]
fn intrinsic_argument_names_types_and_modes_are_checked() {
    for expression in [
        "(#call #usize::lt ((left 1usize)))",
        "(#call #usize::lt ((left 1usize) (right 2usize) (wrong 0usize)))",
        "(#call #usize::lt ((left 1usize) (left 2usize)))",
        "(#call #usize::lt ((left 1usize) (right false)))",
        "(#call #u64::add ((left 1u64) (right 2u64)))",
        "(#call #u64::eq-wrap ((left 1u64) (right 2u64)))",
        "(#call #bool::not ((value 1u64)))",
        "(#call #bool::and ((left true) (right true)))",
        "(#unsafe (#unsafe-call #usize::lt ((left 1usize) (right 2usize))))",
    ] {
        let source = format!("#fn main () () {expression} (#return ())\n");
        assert!(check(&source).is_err(), "accepted {expression}");
    }
}

#[test]
fn intrinsic_calls_and_direct_comparisons_share_exact_claims() {
    let source = r#"#fn read ((values (#ref (#array #u64 4))) (index #usize)) #u64
        (#requires (#call #usize::lt ((right 4usize) (left index))))
        (#return (#index-proven values index))
#fn use ((values (#ref (#array #u64 4))) (index #usize)) #u64
          (#return (#if-valid (#usize::lt index 4usize)
            (#call read ((values values) (index index))) 0u64))
"#;
    check(source).unwrap();
    let reversed = source
        .replace(
            "(#usize::lt index 4usize)",
            "(#call #usize::lt ((left index) (right 4usize)))",
        )
        .replace(
            "(#requires (#call #usize::lt ((right 4usize) (left index))))",
            "(#requires (#usize::lt index 4usize))",
        );
    check(&reversed).unwrap();
    assert!(
        check(&source.replace("#usize::lt index 4usize", "#usize::lt index 2usize"))
            .unwrap_err()
            .contains("missing evidence")
    );
}

#[test]
fn generated_array_get_uses_an_explicit_comparison_contract() {
    let source = include_str!("../examples/generated_array.lim");
    check(source).unwrap();
    for checks in [false, true] {
        assert_eq!(execute(source, checks), 42);
    }
    assert!(
        check(&source.replace("          (#call widen ((index index)))\n", ""))
            .unwrap_err()
            .contains("missing evidence")
    );
}

#[test]
fn generated_validator_needs_its_explicit_claim_bridge() {
    let source = r#"#generate #array ((element #u64) (length 4) (name Values))
#fn main () #u64
          (#let values Values (#array-of 1 42 3 4)) (#let index #usize 1usize)
          (#return (#if-valid (#call Values::in-bounds ((index index)))
            (#block (#call Values::prove-in-bounds ((index index)))
              (#call Values::get ((values (#borrow values)) (index index)))) 0u64))
"#;
    assert_eq!(execute(source, true), 42);
    assert!(
        check(&source.replace("(#call Values::prove-in-bounds ((index index)))", ""))
            .unwrap_err()
            .contains("missing evidence")
    );
}

#[test]
fn generated_borrows_keep_mutation_and_ownership_checks() {
    let source = r#"#generate #array ((element #u64) (length 2) (name Values))
#fn main () #u64
          (#let-mut values Values (#array-of 1 2)) (#let index #usize 1usize)
          (#return (#if-valid (#call #usize::lt ((left index) (right 2usize)))
            (#block
              (#let slot (#ref-mut #u64) (#call Values::borrow-mut ((values (#borrow-mut values)) (index index))))
              (#deref-set slot 42u64) (#drop slot)
              (#call Values::get ((values (#borrow values)) (index index)))) 0u64))
"#;
    assert_eq!(execute(source, false), 42);
    assert_eq!(execute(source, true), 42);
    let overlap = source.replace("(#deref-set slot 42u64) (#drop slot)", "(#let shared (#ref #u64) (#call Values::borrow ((values (#borrow values)) (index index)))) (#deref-set slot 42u64) (#drop shared)");
    assert!(check(&overlap).is_err());
    let linear = "#struct Resource (#linear) ((value #u64))\n#generate #array ((element Resource) (length 2) (name Resources))\n";
    check(linear).unwrap();
    let program = lim::parse_program(linear).unwrap();
    assert!(!program.items.iter().any(|item| matches!(item, lim::Item::Function(function) if function.name.ends_with("Resources::get"))));
    assert!(program.items.iter().any(|item| matches!(item, lim::Item::Function(function) if function.name.ends_with("Resources::borrow-mut"))));
}

#[test]
fn generated_array_lengths_are_literals_and_empty_bounds_stay_empty() {
    for length in ["-1", "false", "unknown", "1.5"] {
        assert!(check(&format!(
            "#generate #array ((element #u64) (length {length}) (name Values))\n"
        ))
        .is_err());
    }
    let source = "#generate #array ((element #u64) (length 0) (name Empty))\n#fn read ((values (#ref Empty)) (index #usize)) #u64 (#return (#call Empty::get ((values values) (index index))))\n";
    assert!(check(source).unwrap_err().contains("missing evidence"));
}
