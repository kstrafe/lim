mod support;
use std::{os::unix::process::ExitStatusExt, process::Command, time::Duration};
fn run(source: &str, instrumented: bool) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("contract-runtime");
    let mut config = lim::CompileConfig::default();
    if instrumented {
        config.set("contracts", "check");
    }
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|e| panic!("{}\n{source}", e.message));
    let executable = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &executable,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    support::run(&mut Command::new(executable), Duration::from_secs(5), 4096)
        .unwrap()
        .0
}
#[test]
fn test_build_checks_false_postcondition_and_production_erases_it() {
    let source = r#"
#fn below-100 ((value #u64)) #bool (#return (#u64::lt value 100u64))
#fn produce () #u64 (#ensures (#call below-100 ((value (#result))))) (#return 200u64)
#fn main () #u64 (#let value #u64 (#call produce ())) (#forget value) (#return 42u64)
"#;
    assert_eq!(run(source, false).code(), Some(42));
    assert_eq!(run(source, true).signal(), Some(4));
}
#[test]
fn test_build_accepts_true_postcondition() {
    let source = r#"#fn below-100 ((value #u64)) #bool (#return (#u64::lt value 100u64))
#fn produce () #u64 (#ensures (#call below-100 ((value (#result))))) (#return 7u64)
#fn main () #u64 (#return (#call produce ()))
"#;
    assert_eq!(run(source, true).code(), Some(7));
}
#[test]
fn assume_never_evaluates_its_predicate_even_in_tests() {
    let source = r#"#fn explosive ((value #u64)) #bool (#return (#panic))
#fn main () #u64 (#assume (#call explosive ((value 42u64)))) (#return 42u64)
"#;
    for mode in [false, true] {
        assert_eq!(run(source, mode).code(), Some(42));
    }
}
#[test]
fn validation_branch_remains_executable_in_production() {
    let source = r#"#fn check-input ((value #u64)) #bool (#return (#u64::lt value 100u64))
#fn main () #u64 (#if-valid (#call check-input ((value 200u64))) (#block (#return 1u64))) (#return 42u64)
"#;
    for mode in [false, true] {
        assert_eq!(run(source, mode).code(), Some(42));
    }
}
#[test]
fn conditional_preservation_checks_only_initially_true_predicates() {
    let source = r#"#fn small ((value (#ref #u64))) #bool (#return (#u64::lt (#deref value) 100u64))
#fn overwrite ((value (#ref-mut #u64))) () (#preserves (#call small ((value value)))) (#deref-set value 200u64) (#return ())
#fn main () #u64 (#let-mut number #u64 7u64) (#call overwrite ((value (#borrow-mut number)))) (#return 42u64)
"#;
    assert_eq!(run(source, false).code(), Some(42));
    assert_eq!(run(source, true).signal(), Some(4));
    assert_eq!(run(&source.replace('7', "207"), true).code(), Some(42));
}

#[test]
fn entry_assertions_are_independent_of_an_assume() {
    let source = r#"#fn small ((value #u64)) #bool (#return (#u64::lt value 100u64))
#fn consume ((value #u64)) () (#requires (#call small ((value value)))) (#return ())
#fn main () #u64 (#let value #u64 200u64) (#assume (#call small ((value value)))) (#call consume ((value value))) (#return 42u64)
"#;
    assert_eq!(run(source, false).code(), Some(42));
    assert_eq!(run(source, true).signal(), Some(4));
}
#[test]
fn old_snapshots_the_entry_scalar_on_every_return() {
    let source = r#"#fn increased ((before #u64) (after #u64)) #bool (#return (#u64::lt before after))
#fn update ((value (#ref-mut #u64)) (early #bool)) ()
        (#ensures (#call increased ((before (#old (#deref value))) (after (#deref value)))))
        (#if early (#block (#deref-set value 2u64) (#return ())))
        (#deref-set value 3u64) (#return ())
#fn main () #u64 (#let-mut number #u64 1u64) (#call update ((value (#borrow-mut number)) (early true))) (#return number)
"#;
    assert_eq!(run(source, true).code(), Some(2));
    assert_eq!(
        run(&source.replace("(early true)", "(early false)"), true).code(),
        Some(3)
    );
    assert_eq!(
        run(
            &source.replace("#let-mut number #u64 1u64", "#let-mut number #u64 9u64"),
            true
        )
        .signal(),
        Some(4)
    );
}
#[test]
fn example_runs_with_contract_assertions() {
    assert_eq!(
        run(include_str!("../examples/contracts.lim"), true).code(),
        Some(42)
    );
}

#[test]
fn explicitly_proven_array_index_runs_in_both_modes() {
    for instrumented in [false, true] {
        assert_eq!(
            run(
                include_str!("../examples/index_contracts.lim"),
                instrumented
            )
            .code(),
            Some(42)
        );
    }
}

#[test]
fn proven_index_elides_production_bounds_checks_and_audits_test_accesses() {
    let scratch = support::Scratch::new("proven-index-emission");
    for source in [
        include_str!("../examples/index_contracts.lim"),
        include_str!("../examples/generated_array.lim"),
    ] {
        for instrumented in [false, true] {
            let mut config = lim::CompileConfig::default();
            if instrumented {
                config.set("contracts", "check");
            }
            let assembly = lim::compile_source_to_assembly(
                source,
                &scratch.path().join("main.lim"),
                &config,
                &scratch.path().join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
            assert_eq!(
                assembly.contains("borrow_array_bounds_failure"),
                instrumented,
                "{assembly}"
            );
        }
    }
}

#[test]
fn instrumented_proven_index_audits_an_assumed_bound() {
    let source = r#"
#fn read ((values (#ref (#array #u64 4))) (index #usize)) #u64
          (#assume (#usize::lt index 4usize))
          (#return (#index-proven values index))
#fn main () #u64
          (#let values (#array #u64 4) (#array (#array #u64 4) 1u64 2u64 3u64 4u64))
          (#return (#call read ((values (#borrow values)) (index 4usize))))
"#;
    assert_eq!(run(source, true).signal(), Some(4));
}

#[test]
fn instrumented_index_proof_helper_audits_its_promise() {
    let source = include_str!("../examples/index_contracts.lim")
        .replace("#usize::lt index 2usize", "#usize::lt index 8usize")
        .replace("(index 1usize)", "(index 6usize)");
    assert_eq!(run(&source, true).signal(), Some(4));
}

#[test]
fn proven_element_borrows_preserve_array_layout_and_borrow_rules() {
    let source = r#"
#fn edit ((values (#ref-mut (#array #u64 4))) (index #usize)) ()
          (#requires (#usize::lt index 4usize))
          (#deref-set (#borrow-mut (#index-proven values index)) 42u64)
          (#return ())
#fn main () #u64
          (#let-mut values (#array #u64 4) (#array (#array #u64 4) 1u64 2u64 3u64 4u64))
          (#let index #usize 2usize)
          (#if-valid (#usize::lt index 4usize)
            (#call edit ((values (#borrow-mut values)) (index index))))
          (#return (#index values 2usize))
"#;
    for instrumented in [false, true] {
        assert_eq!(run(source, instrumented).code(), Some(42));
    }
}

#[test]
fn proven_index_reads_multiword_elements() {
    let source = r#"
#fn read ((values (#ref (#array (#tuple #u64 #u64) 2))) (index #usize)) #u64
          (#requires (#usize::lt index 2usize))
          (#return (#get (#index-proven values index) 1))
#fn main () #u64
          (#let values (#array (#tuple #u64 #u64) 2)
            (#array (#array (#tuple #u64 #u64) 2)
              (#tuple (#tuple #u64 #u64) 1u64 2u64)
              (#tuple (#tuple #u64 #u64) 3u64 42u64)))
          (#let index #usize 1usize)
          (#if-valid (#usize::lt index 2usize)
            (#block (#return (#call read ((values (#borrow values)) (index index))))))
          (#return 0u64)
"#;
    for instrumented in [false, true] {
        assert_eq!(run(source, instrumented).code(), Some(42));
    }
}
#[test]
fn fixed_field_borrow_is_checked_in_both_build_modes() {
    let source = r#"#fn small ((value (#ref #u64))) #bool (#return (#u64::lt (#deref value) 100u64))
#type Small (#where (value #u64) (#call small ((value (#borrow value)))))
#struct Holder () ((number Small))
#fn edit ((holder (#ref-mut Holder))) ()
          (#let slot (#ref-mut #u64) (#borrow-mut (#get holder number)))
          (#deref-set slot 42u64)
          (#assume (#call small ((value slot))))
          (#return ())
#fn main () #u64 (#let number #u64 7u64)
          (#assume (#call small ((value (#borrow number)))))
          (#let-mut holder Holder (#struct-literal Holder ((number number))))
          (#call edit ((holder (#borrow-mut holder))))
          (#let answer #u64 (#get holder number)) (#forget holder) (#return answer)
"#;
    for mode in [false, true] {
        assert_eq!(run(source, mode).code(), Some(42));
    }
}
#[test]
fn returned_element_reference_defers_the_owner_restore_check() {
    let source = r#"#fn small ((value (#ref #u64))) #bool (#return (#u64::lt (#deref value) 100u64))
#type Small (#where (value #u64) (#call small ((value (#borrow value)))))
#struct Holder () ((number Small))
#fn slot ((holder (#ref-mut Holder))) (#ref-mut #u64) (#return (#borrow-mut (#get holder number)))
#fn edit ((holder (#ref-mut Holder))) ()
          (#let item (#ref-mut #u64) (#call slot ((holder holder))))
          (#deref-set item 42u64) (#assume (#call small ((value item)))) (#return ())
#fn main () #u64 (#let number #u64 7u64) (#assume (#call small ((value (#borrow number)))))
          (#let-mut holder Holder (#struct-literal Holder ((number number))))
          (#call edit ((holder (#borrow-mut holder))))
          (#let answer #u64 (#get holder number)) (#forget holder) (#return answer)
"#;
    for mode in [false, true] {
        assert_eq!(run(source, mode).code(), Some(42));
    }
}
#[test]
fn contracts_compose_with_existing_async_programs() {
    let mut source = include_str!("../examples/async_fn.lim").to_owned();
    source = source.replace(
        "(#u64::add-wrap total offset)",
        "(#call #u64::add-wrap ((right offset) (left total)))",
    );
    source.push_str("\n#generate #array ((element #u64) (length 4) (name AsyncValues))\n#fn generated-array-read ((values (#ref AsyncValues)) (index #usize)) #u64 (#requires (#call #usize::lt ((left index) (right 4usize)))) (#return (#call AsyncValues::get ((values values) (index index))))\n");
    source.push_str("\n#fn contract-test-predicate ((value #u64)) #bool (#return (#u64::lt value 100u64))\n#fn contract-test-client ((value #u64)) () (#requires (#call contract-test-predicate ((value value)))) (#return ())\n");
    source.push_str("\n#fn contract-test-index ((values (#ref (#array #u64 4))) (index #usize)) #u64 (#requires (#usize::lt index 4usize)) (#return (#index-proven values index))\n");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/async_fn.lim");
    let scratch = support::Scratch::new("async-contract-check");
    lim::compile_source_to_assembly(
        &source,
        &root,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|e| panic!("{}", e.message));
    let missing = source.replace("(#requires (#usize::lt index 4usize))", "");
    let error = lim::compile_source_to_assembly(
        &missing,
        &root,
        &lim::CompileConfig::default(),
        &scratch.path().join("missing-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("the final async program must reject a missing index bound");
    assert!(
        error.message.contains("missing evidence"),
        "{}",
        error.message
    );
    let mut audited_source = source
        .replace("#fn main () #u64", "#fn async-original-main () #u64")
        .replace(
            "(#requires (#usize::lt index 4usize))",
            "(#assume (#usize::lt index 4usize))",
        );
    audited_source.push_str(
        r#"
#fn main () #u64
          (#let values (#array #u64 4) (#array (#array #u64 4) 1u64 2u64 3u64 4u64))
          (#return (#call contract-test-index ((values (#borrow values)) (index 4usize))))
"#,
    );
    let mut config = lim::CompileConfig::default();
    config.set("contracts", "check");
    let assembly = lim::compile_source_to_assembly(
        &audited_source,
        &root,
        &config,
        &scratch.path().join("audited-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    let executable = scratch.path().join("audited-program");
    lim::link_native_binary(
        &assembly,
        &executable,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, _) =
        support::run(&mut Command::new(executable), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.signal(), Some(4));
}
#[test]
fn a_whole_collection_can_be_validated_after_an_element_borrow() {
    let source = r#"#fn ordered ((values (#ref (#array #u64 2)))) #bool
          (#return (#u64::le (#index (#deref values) 0usize) (#index (#deref values) 1usize)))
#type Ordered (#where (value (#array #u64 2)) (#call ordered ((values (#borrow value)))))
#struct Store () ((values Ordered))
#fn main () #u64
          (#let values (#array #u64 2) (#array (#array #u64 2) 7u64 9u64))
          (#assume (#call ordered ((values (#borrow values)))))
          (#let-mut store Store (#struct-literal Store ((values values))))
          (#let item (#ref-mut #u64) (#borrow-mut (#index (#get store values) 1usize)))
          (#deref-set item 42u64)
          (#if-valid (#call ordered ((values (#borrow (#get store values))))) () (#panic))
          (#let answer #u64 (#index (#get store values) 1usize))
          (#forget store) (#return answer)
"#;
    for mode in [false, true] {
        assert_eq!(run(source, mode).code(), Some(42));
    }
    let assumed = source.replace(
        "(#if-valid (#call ordered ((values (#borrow (#get store values))))) () (#panic))",
        "(#assume (#call ordered ((values (#borrow (#get store values))))))",
    );
    for mode in [false, true] {
        assert_eq!(run(&assumed, mode).code(), Some(42));
    }
}
