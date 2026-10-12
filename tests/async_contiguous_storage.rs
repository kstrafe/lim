mod support;

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
fn whole_borrow_after_field_restoration_keeps_sibling_address_across_await() {
    run(include_str!("fixtures/async_partial_whole_borrow.lim"));
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
