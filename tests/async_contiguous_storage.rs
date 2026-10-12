mod support;

#[test]
fn ordinary_typed_contiguous_payload_preserves_reference_field_address_natively() {
    run_ordinary_typed_payload(false);
}

#[test]
fn heap_typed_contiguous_payload_preserves_reference_field_address_natively() {
    run_ordinary_typed_payload(true);
}

#[test]
fn untagged_stack_owner_preserves_reference_field_address_and_provenance() {
    run_ordinary_typed_owner(false, false);
}

#[test]
fn untagged_heap_owner_preserves_reference_field_address_and_provenance() {
    run_ordinary_typed_owner(true, false);
}

#[test]
fn untagged_stack_owner_preserves_exclusive_contained_reference() {
    run_ordinary_typed_owner(false, true);
}

#[test]
fn untagged_heap_owner_preserves_exclusive_contained_reference() {
    run_ordinary_typed_owner(true, true);
}

fn run_ordinary_typed_owner(on_heap: bool, exclusive: bool) {
    let source = include_str!("fixtures/partial_reference_typed_owner.lim").to_owned();
    let parsed = lim::parse_program(&source).unwrap();
    assert!(!parsed
        .items
        .iter()
        .any(|item| matches!(item, lim::Item::Enum { .. })));
    let source = if exclusive {
        source
            .replace("kept (#ref #u64)", "kept (#ref-mut #u64)")
            .replace("kept (#borrow seed)", "kept (#borrow-mut seed)")
            .replace("(#ref (#ref #u64))", "(#ref (#ref-mut #u64))")
            .replace("(#pin-ref (#ref #u64))", "(#pin-ref (#ref-mut #u64))")
            .replace(
                "(#deref (#get restored kept))",
                "(#deref (#deref selected))",
            )
    } else {
        source
    };
    let source = if on_heap {
        source
            .replace("(#let-mut storage Owner", "(#let allocation (#ptr-mut Owner) (#unsafe (#linux-syscall (#ptr-mut Owner)\n        9usize (0usize (#size-of Owner) 3usize 34usize -1i64 0usize))))\n      (#let initial Owner")
            .replace("(#let owner", "(#let-mut storage (#pin-own Owner) (#unsafe (#pin-own-of allocation initial)))\n      (#let owner")
            .replace("(#pin-borrow-mut storage)", "(#pin-own-borrow-mut storage)")
            .replace("(#forget storage)", "(#let released (#ptr-mut Owner) (#unsafe (#pin-release storage)))\n      (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize\n        (released (#size-of Owner)))) 0i64))")
    } else {
        source
    };
    let scratch = support::Scratch::new("untagged-contiguous-reference-owner");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let mut previous = None;
    for label in ["cold", "warm"] {
        let assembly = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            target,
        )
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, &source, "input.lim")));
        if let Some(previous) = &previous {
            assert_eq!(&assembly, previous);
        }
        let binary = scratch.path().join(label);
        lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
        let (status, stdout, stderr) = support::run(
            &mut std::process::Command::new(binary),
            std::time::Duration::from_secs(5),
            4096,
        )
        .unwrap();
        assert_eq!(status.code(), Some(42), "{stderr:?}");
        assert!(stdout.is_empty() && stderr.is_empty());
        previous = Some(assembly);
    }
    for invalid in [
        source.replace("(#let kept", "(#set seed 99u64)\n      (#let kept"),
        source.replace("(#let selected", "(#unsafe (#call restore-item (: item (#pin-borrow-mut (#get owner item)))))\n      (#let selected"),
    ] {
        let error = lim::compile_source_to_assembly(
            &invalid, &scratch.path().join("invalid.lim"), &lim::CompileConfig::default(),
            &scratch.path().join("invalid-cache"), target,
        ).expect_err("untagged storage must not discard alias protection");
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        assert!(error.span.is_some(), "{error:?}");
    }
}

fn run_ordinary_typed_payload(on_heap: bool) {
    let source = include_str!("fixtures/partial_reference_typed_payload.lim");
    let scratch = support::Scratch::new("typed-contiguous-reference-payload");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let heap = source
        .replace(
            "(#let-mut storage Storage",
            "
      (#let allocation (#ptr-mut Storage) (#unsafe (#linux-syscall (#ptr-mut Storage)
        9usize (0usize (#size-of Storage) 3usize 34usize -1i64 0usize))))
      (#let initial Storage",
        )
        .replace(
            "(#let owner",
            "
      (#let-mut storage (#pin-own Storage) (#unsafe (#pin-own-of allocation initial)))
      (#let owner",
        )
        .replace("(#pin-borrow-mut storage)", "(#pin-own-borrow-mut storage)")
        .replace(
            "(#forget storage)",
            "
      (#let released (#ptr-mut Storage) (#unsafe (#pin-release storage)))
      (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize
        (released (#size-of Storage)))) 0i64))",
        );
    let (kind, source) = if on_heap {
        ("heap", heap.as_str())
    } else {
        ("stack", source)
    };
    {
        let mut previous = None;
        for label in ["cold", "warm"] {
            let assembly = lim::compile_source_to_assembly(
                source,
                &scratch.path().join("input.lim"),
                &lim::CompileConfig::default(),
                &scratch.path().join("cache"),
                target,
            )
            .unwrap();
            if let Some(previous) = &previous {
                assert_eq!(&assembly, previous);
            }
            let binary = scratch.path().join(format!("{kind}-{label}"));
            lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
            let (status, stdout, stderr) = support::run(
                &mut std::process::Command::new(binary),
                std::time::Duration::from_secs(5),
                4096,
            )
            .unwrap();
            assert_eq!(status.code(), Some(42), "{stderr:?}");
            assert!(stdout.is_empty() && stderr.is_empty());
            previous = Some(assembly);
        }
    }
}

#[test]
fn source_checks_reject_incomplete_and_conflicting_whole_borrows() {
    let source = include_str!("fixtures/async_partial_whole_borrow.lim");
    let missing = source.replace(
        "(#set-field owner item (#struct-literal Token (: value 2u64)))",
        "",
    );
    let exclusive = source
        .replace(
            "whole (#ref Owner) (#borrow owner)",
            "whole (#ref-mut Owner) (#borrow-mut owner)",
        )
        .replace("(: owner (#ref Owner))", "(: owner (#ref-mut Owner))");
    let scratch = support::Scratch::new("async-contiguous-rejected");
    for invalid in [&missing, &exclusive] {
        for _ in 0..2 {
            let error = lim::compile_source_to_assembly(
                invalid,
                &scratch.path().join("main.lim"),
                &lim::CompileConfig::default(),
                &scratch.path().join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_err();
            assert!(
                matches!(
                    error.code,
                    lim::DiagnosticCode::Borrow | lim::DiagnosticCode::Linear
                ),
                "{error:?}"
            );
            assert!(error.span.is_some(), "{error:?}");
        }
    }
}

#[test]
fn whole_clone_preserves_the_original_owner_and_retained_address() {
    run(&cloned_source());
}

#[test]
fn cancellation_after_whole_clone_still_exports_the_original_linear_field() {
    let source = cloned_source().replace(
        "(#forget copied)",
        "(#forget copied)
      (#let second-ready () (#await () Step Pending Ready step-poll Start))
      (#forget second-ready)",
    );
    let prefix = source.split_once("(#fn main () #u64").unwrap().0;
    run(&format!(
        "{prefix}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut frame Work-frame (#call work (:)))
        (#let first Work-poll-result (#call work-poll
          (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll
          (: task pending : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result second (#unreachable))
        (#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task next)))
        (#let-else (Work-frame-cleanup-owner.item-full original)
          Work-frame-cleanup-owner.item (#get cleanup owner.item) (#unreachable))
        (#assert (#u64.== (#get original value) 2u64))
        (#forget original) (#forget cleanup)
        (#forget pending) (#forget next) (#forget frame)
        (#return 42u64))"
    ));
}

fn cloned_source() -> String {
    let source = include_str!("fixtures/async_partial_whole_borrow.lim");
    let hooks = "
      (#fn Token-clone (: original Token) Token
        (#let value #u64 (#get original value))
        (#forget original)
        (#return (#struct-literal Token (: value (#u64.+.wrap value 10u64)))))
      (#fn Owner-clone (: original Owner) Owner
        (#let kept #u64 (#get original kept))
        (#let item Token (#clone (#get original item)))
        (#forget original)
        (#return (#struct-literal Owner (: kept kept : item item))))";
    format!("{hooks}\n{source}").replace(
        "(#let whole (#ref Owner)",
        "(#let copied Owner (#clone owner))
         (#assert (#u64.== (#get (#get copied item) value) 12u64))
         (#forget copied)\n    (#let whole (#ref Owner)",
    )
}

#[test]
fn whole_borrow_after_field_restoration_keeps_sibling_address_across_await() {
    run(include_str!("fixtures/async_partial_whole_borrow.lim"));
}

#[test]
#[ignore = "reference-bearing contiguous owner storage is not implemented yet"]
fn reference_field_keeps_address_and_provenance_after_sibling_restoration() {
    run(include_str!(
        "fixtures/async_partial_reference_whole_borrow.lim"
    ));
}

#[test]
fn unsupported_reference_field_whole_view_fails_at_the_source_borrow() {
    let source = include_str!("fixtures/async_partial_reference_whole_borrow.lim");
    let scratch = support::Scratch::new("async-reference-contiguous-gate");
    for _ in 0..2 {
        let error = lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(
            error.message.contains("requires contiguous owning storage"),
            "{error:?}"
        );
        let span = error.span.expect("original whole-borrow source span");
        assert_eq!(&source[span.start..span.end], "(#borrow owner)");
    }
}

#[test]
fn selected_whole_owner_keeps_branch_identity_with_contiguous_storage() {
    let source = include_str!("fixtures/async_partial_whole_borrow.lim")
        .replace("(#fn work () #u64", "(#fn work (: flag #bool) #u64")
        .replace(
            "(#let whole (#ref Owner) (#borrow owner))",
            "
          (#let other Owner (#struct-literal Owner (: kept 40u64
            : item (#struct-literal Token (: value 2u64)))))
          (#let whole (#ref Owner) (#if flag (#borrow owner) (#borrow other)))",
        )
        .replace(
            "(#ref-ptr kept)",
            "(#if flag (#ref-ptr kept)
            (#ref-ptr (#borrow (#get other kept))))",
        )
        .replace("(#forget owner)", "(#forget owner) (#forget other)");
    for flag in ["true", "false"] {
        run(&source.replace("(#call work (:))", &format!("(#call work (: flag {flag}))")));
    }
}

#[test]
fn heap_owned_whole_borrow_preserves_the_same_contiguous_address() {
    let source = include_str!("fixtures/async_partial_whole_borrow.lim")
        .replace(
            "(#let-mut frame Work-frame (#call work (:)))",
            "
          (#let pointer (#ptr-mut Work-frame) (#unsafe (#linux-syscall (#ptr-mut Work-frame)
            9usize (0usize (#size-of Work-frame) 3usize 34usize -1i64 0usize))))
          (#let initial Work-frame (#call work (:)))
          (#let-mut frame (#pin-own Work-frame) (#unsafe (#pin-own-of pointer initial)))",
        )
        .replace("(#pin-borrow-mut frame)", "(#pin-own-borrow-mut frame)")
        .replace(
            "(#forget frame)",
            "
          (#forget pending)
          (#let raw (#ptr-mut Work-frame) (#unsafe (#pin-release frame)))
          (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize
            (raw (#size-of Work-frame)))) 0i64))",
        );
    run(&source);
}

fn run(source: &str) {
    let scratch = support::Scratch::new("async-contiguous");
    let input = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let cold = lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &cache,
        target,
    )
    .unwrap_or_else(|error| {
        let hunk = error.span.and_then(|span| {
            error.source_text.as_ref().map(|source| {
                &source[span.start.saturating_sub(100)..(span.end + 100).min(source.len())]
            })
        });
        panic!(
            "{:?}: {} at {:?}: {:?}",
            error.code, error.message, error.span, hunk
        )
    });
    let warm = lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &cache,
        target,
    )
    .unwrap();
    assert_eq!(cold, warm);
    let generated = std::fs::read_dir(scratch.path().join("generated"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "lim")
        })
        .map(|entry| std::fs::read_to_string(entry.path()).unwrap())
        .find(|text| text.contains("aggregate-words"))
        .unwrap();
    assert!(generated.contains("aggregate-words"));
    assert!(generated.contains("(#array Owner 0)"));
    assert!(generated.contains("#word-view"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(&cold, &binary, &[], &[], target).unwrap();
    let (status, _, stderr) = support::run(
        &mut std::process::Command::new(binary),
        std::time::Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}
