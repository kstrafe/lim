//! Exercise dispatch through the internal encoder/linker, not just assembly.
mod support;

use std::{os::unix::process::ExitStatusExt, process::Command, time::Duration};

fn compile_and_run(source: &str) -> String {
    let scratch = support::Scratch::new("enum-jump-table");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
    .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    // Every indirect arm must remain visible to whole-program stack bounds.
    let report = lim::stack_usage_report(&assembly).unwrap();
    assert!(report.contains("at most"), "{report}");
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}\n{source}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
    assembly
}

fn fieldless_source(tags: &[u64]) -> String {
    let variants = tags
        .iter()
        .enumerate()
        .map(|(index, tag)| format!("(Variant{index} {tag})"))
        .collect::<Vec<_>>()
        .join(" ");
    // Neither declaration nor arm order needs to equal tag order.
    let arms = (0..tags.len())
        .rev()
        .map(|index| format!("(#case Variant{index} {}u64)", index + 10))
        .collect::<Vec<_>>()
        .join(" ");
    let checks = (0..tags.len())
        .map(|index| {
            format!(
                "(#assert (#u64.== (#call dispatch (: value Variant{index})) {}u64))",
                index + 10
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "(#enum Tag ({variants}))
        (#fn dispatch (: value Tag) #u64 (#return (#match value {arms})))
        (#fn main () #u64 {checks} (#return 42u64))"
    )
}

#[test]
fn contiguous_tags_dispatch_in_tag_order_including_full_width_ranges() {
    for tags in [
        vec![0, 1, 2, 3],
        vec![9, 7, 10, 8],
        vec![0x8000_0000, 0x8000_0001, 0x8000_0002, 0x8000_0003],
        vec![u64::MAX - 2, u64::MAX, u64::MAX - 3, u64::MAX - 1],
    ] {
        let assembly = compile_and_run(&fieldless_source(&tags));
        assert!(assembly.contains("enum_jump_table"), "{assembly}");
        assert!(assembly.contains("movsxd rax, DWORD PTR [r11+rax*4]"));
        assert!(assembly.contains("jmp r11"));
        assert!(!assembly.contains("cmp QWORD PTR [rsp]"));
    }
}

#[test]
fn small_sparse_and_few_destination_matches_keep_direct_branches() {
    for tags in [vec![0, 1, 2], vec![0, 2, 4, 6], vec![0, 1, 2, u64::MAX]] {
        let assembly = compile_and_run(&fieldless_source(&tags));
        assert!(!assembly.contains("enum_jump_table"));
        assert!(assembly.contains("cmp QWORD PTR [rsp]"));
    }
    let assembly = compile_and_run(
        "(#enum Tag (A B C D E))
        (#fn dispatch (: value Tag) #u64 (#return (#match value (#case A 1u64) (#case _ 42u64))))
        (#fn main () #u64 (#return (#call dispatch (: value E))))",
    );
    assert!(!assembly.contains("enum_jump_table"));
}

#[test]
fn wildcard_entries_use_the_original_default_arm() {
    let assembly = compile_and_run(
        "(#enum Tag (A B C D E F))
        (#fn dispatch (: value Tag) #u64 (#return (#match value
          (#case D 4u64) (#case B 2u64) (#case A 1u64) (#case _ 42u64))))
        (#fn main () #u64
          (#assert (#u64.== (#call dispatch (: value A)) 1u64))
          (#assert (#u64.== (#call dispatch (: value B)) 2u64))
          (#assert (#u64.== (#call dispatch (: value D)) 4u64))
          (#assert (#u64.== (#call dispatch (: value C)) 42u64))
          (#assert (#u64.== (#call dispatch (: value E)) 42u64))
          (#return (#call dispatch (: value F))))",
    );
    assert!(assembly.contains("enum_jump_table"));
    assert!(!assembly.contains("cmp QWORD PTR [rsp]"));
}

#[test]
fn guards_and_refutable_payloads_preserve_ordered_fallback() {
    for first in [
        "(#case (A payload) (#when (#u64.== payload 7u64)) 17u64)",
        "(#case (A 7) 17u64)",
    ] {
        let source = format!(
            "(#enum Tag ((A #u64) B C D))
            (#fn dispatch (: value Tag) #u64 (#return (#match value
              {first} (#case B 20u64)
              (#case C 30u64) (#case D 40u64) (#case _ 42u64))))
            (#fn main () #u64
              (#assert (#u64.== (#call dispatch (: value (A 7u64))) 17u64))
              (#assert (#u64.== (#call dispatch (: value B)) 20u64))
              (#assert (#u64.== (#call dispatch (: value C)) 30u64))
              (#assert (#u64.== (#call dispatch (: value D)) 40u64))
              (#return (#call dispatch (: value (A 42u64)))))"
        );
        let assembly = compile_and_run(&source);
        assert!(assembly.contains("enum_jump_table"));
        assert!(assembly.contains("cmp QWORD PTR [rsp]"));
    }
}

#[test]
fn wildcard_guard_failure_does_not_skip_later_variants() {
    let assembly = compile_and_run(
        "(#enum Tag (A B C D E))
        (#fn dispatch (: value Tag) #u64 (#return (#match value
          (#case A 10u64) (#case B 20u64) (#case C 30u64)
          (#case _ (#when false) 0u64) (#case D 40u64) (#case E 42u64))))
        (#fn main () #u64
          (#assert (#u64.== (#call dispatch (: value A)) 10u64))
          (#assert (#u64.== (#call dispatch (: value D)) 40u64))
          (#return (#call dispatch (: value E))))",
    );
    assert!(assembly.contains("enum_jump_table"));
}

#[test]
fn guarded_repeated_variants_evaluate_guards_once_and_only_for_matching_tags() {
    let assembly = compile_and_run(
        "(#enum Tag ((A #u64) B C D))
        (#fn dispatch (: value Tag : count (#ref-mut #u64)) #u64
          (#return (#match value
            (#case (A first) (#when (#block
              (#deref-set count (#u64.+.wrap (#deref count) 1u64)) false)) 0u64)
            (#case B 20u64) (#case (A selected) selected)
            (#case C 30u64) (#case D 40u64))))
        (#fn main () #u64
          (#let-mut checks #u64 0u64)
          (#assert (#u64.== (#call dispatch (: value B : count (#borrow-mut checks))) 20u64))
          (#assert (#u64.== checks 0u64))
          (#let answer #u64 (#call dispatch (: value (A 42u64) : count (#borrow-mut checks))))
          (#assert (#u64.== checks 1u64)) (#return answer))",
    );
    assert!(assembly.contains("enum_jump_table"));
}

#[test]
fn invalid_discriminants_trap_before_indexing_the_table() {
    let scratch = support::Scratch::new("enum-jump-table-invalid-tag");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    for (tags, invalid) in [
        (vec![10, 11, 12, 13], vec![9, 14, u64::MAX]),
        (
            vec![u64::MAX - 3, u64::MAX - 2, u64::MAX - 1, u64::MAX],
            vec![0, u64::MAX - 4],
        ),
    ] {
        let assembly = lim::compile_source_to_assembly(
            &fieldless_source(&tags),
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            target,
        )
        .unwrap();
        for invalid in invalid {
            // Corrupt just the staged tag at the backend boundary. Safe Lim
            // cannot construct this invalid value; no unsafe source loophole
            // or invalid enum-to-integer cast is needed for the regression.
            let poisoned = assembly.replacen(
                "mov rax, QWORD PTR [rsp]",
                &format!("mov rax, {invalid}"),
                1,
            );
            assert_ne!(poisoned, assembly);
            let binary = scratch.path().join("invalid");
            lim::link_native_binary(&poisoned, &binary, &[], &[], target).unwrap();
            let (status, stdout, stderr) =
                support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
            assert_eq!(status.signal(), Some(4), "tag {invalid}: {status:?}");
            assert!(stdout.is_empty());
            assert!(stderr.is_empty());
        }
    }
}

#[test]
fn or_patterns_keep_existing_branch_semantics() {
    let assembly = compile_and_run(
        "(#enum Tag (A B C D E))
        (#fn dispatch (: value Tag) #u64 (#return (#match value
          (#case (#or A B) 42u64) (#case C 3u64) (#case D 4u64) (#case E 5u64))))
        (#fn main () #u64 (#return (#call dispatch (: value B))))",
    );
    assert!(!assembly.contains("enum_jump_table"));
}

#[test]
fn large_payloads_and_indirect_aggregate_destinations_survive_table_dispatch() {
    let assembly = compile_and_run("(#enum Tag ((A (#array #u64 10))
          (B (#array #u64 10)) (C (#array #u64 10)) (D (#array #u64 10))))
        (#fn make (: value #u64) Tag (#return (D (#array-repeat value))))
        (#fn dispatch (: value Tag) Tag (#return (#match value
          (#case (A first) (A first)) (#case (B second) (B second))
          (#case (C third) (C third)) (#case (D fourth) (D fourth)))))
        (#fn main () #u64
          (#let owner Tag (B (#array-repeat 42u64)))
          (#let result Tag (#call dispatch (: value owner)))
          (#let made Tag (#call make (: value 42u64)))
          (#let other Tag (#call dispatch (: value made)))
          (#let first-value #u64 (#match result
            (#case (A fifth) (#index fifth 9u64)) (#case (B sixth) (#index sixth 9u64))
            (#case (C seventh) (#index seventh 9u64)) (#case (D eighth) (#index eighth 9u64))))
          (#assert (#u64.== first-value 42u64))
          (#return (#match other
            (#case (A ninth) (#index ninth 9u64)) (#case (B tenth) (#index tenth 9u64))
            (#case (C eleventh) (#index eleventh 9u64)) (#case (D twelfth) (#index twelfth 9u64)))))");
    assert!(assembly.contains("enum_jump_table"));
}

#[test]
fn computed_and_static_scrutinees_and_float_results_preserve_staging() {
    let assembly = compile_and_run(
        "(#enum Tag ((A #f64) (B #f64) (C #f64) (D #f64)))
        (#static Stored Tag (C 42.0f64))
        (#fn make (: count (#ref-mut #u64)) Tag
          (#deref-set count (#u64.+.wrap (#deref count) 1u64))
          (#return (D 42.0f64)))
        (#fn main () #u64
          (#let-mut count #u64 0u64)
          (#let number #f64 (#match (#call make (: count (#borrow-mut count)))
            (#case (A first) first) (#case (B second) second)
            (#case (C third) third) (#case (D fourth) fourth)))
          (#assert (#u64.== count 1u64))
          (#assert (#f64.== number 42.0f64))
          (#let global-number #f64 (#unsafe (#match Stored
            (#case (A fifth) fifth) (#case (B sixth) sixth)
            (#case (C seventh) seventh) (#case (D eighth) eighth))))
          (#return (#as global-number #u64)))",
    );
    assert!(assembly.contains("enum_jump_table"));
}
