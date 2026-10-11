mod support;

use std::{fs, process::Command, time::Duration};

// Prove the ordinary-code boundary before choosing a public naming/interface
// contract. No async-specific ownership permission is used by these helpers.
#[test]
fn finalized_frame_copy_parameter_can_be_replaced_in_the_same_storage() {
    let prefix = include_str!("../examples/async_fn_self_reference.lim")
        .split("(#fn main")
        .next()
        .unwrap()
        .replace("read-after-await", "work")
        .replace("Read-after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait")
        .replace(": access (: owner work-owner)", "");
    let source = format!("{prefix}
      (#fn main () #u64 (#let waker #u64 0u64)
        (#let-mut frame Work-frame (#call work (: owner (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 40u64 : right 5u64)))))))
        (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let answer #u64 (#match second (#case (work-ready result) result)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#return answer))");
    let scratch = support::Scratch::new("async-finalized-frame-restoration");
    let path = scratch.path().join("input.lim");
    let output = scratch.path().join("generated");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    lim::write_generated_sources_from_path_with_config_and_cache(
        &source,
        &path,
        &output,
        &config,
        &scratch.path().join("cache"),
    )
    .unwrap();
    let artifact = fs::read_dir(&output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|text| text.contains("(#fn work-poll "))
        .unwrap();
    assert!(!artifact.contains("(#fn work-owner-read "));
    assert!(!artifact.contains("(#fn work-owner-replace "));
    // The same ordinary helper must work with the source actually reused from
    // disk, not only the first emission's in-memory analysis identities.
    lim::write_generated_sources_from_path_with_config_and_cache(
        &source,
        &path,
        &output,
        &config,
        &scratch.path().join("cache"),
    )
    .unwrap();
    let warm_artifact = fs::read_dir(&output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|text| text.contains("(#fn work-poll "))
        .unwrap();
    assert_eq!(warm_artifact, artifact);
    let invocation = lim::parse(&source)
        .unwrap()
        .into_iter()
        .find(|node| source[node.span.start..node.span.end].starts_with("(@#async-fn-pinned"))
        .unwrap();
    let standalone = format!(
        "{}\n{artifact}\n{}",
        &source[..invocation.span.start],
        &source[invocation.span.end..]
    );
    let program = lim::parse_program(&standalone).unwrap();
    lim::check_types(&program).unwrap();
    let fields = program
        .items
        .iter()
        .find_map(|item| match item {
            lim::Item::Struct { name, fields, .. } if name == "Work-frame" => Some(fields),
            _ => None,
        })
        .unwrap();
    let mut assertions = Vec::new();
    let mut owner = None;
    for field in fields {
        let lim::Type::Named(cell) = &field.ty else {
            continue;
        };
        let variants = program
            .items
            .iter()
            .find_map(|item| match item {
                lim::Item::Enum { name, variants, .. } if name == cell => Some(variants),
                _ => None,
            })
            .unwrap();
        let empty = variants
            .iter()
            .find(|variant| variant.fields.is_empty())
            .unwrap();
        let full = variants
            .iter()
            .find(|variant| !variant.fields.is_empty())
            .unwrap();
        if full.fields == [lim::Type::Named("Owner".into())] {
            owner = Some((
                field.name.clone(),
                cell.clone(),
                empty.name.clone(),
                full.name.clone(),
            ));
        } else {
            assertions.push(format!(
                "(#assert (#variant-is (#pin-borrow (#get task {})) {}))",
                field.name, empty.name
            ));
        }
    }
    let (field, cell, empty, full) = owner.unwrap();
    let guards = assertions.join("\n");
    let helpers = format!(
        "(#fn replace-owner (: task (#pin-ref-mut Work-frame) : value Owner) ()
      (#assert (#u32.== (#get task pc) 4294967295u32)) {}
      (#let target (#pin-ref-mut {cell}) (#pin-borrow-mut (#get task {field})))
      (#let previous {cell} (#unsafe (#pin-read target)))
      (#match previous (#case {empty} ()) (#case ({full} occupied) (#forget occupied)))
      (#unsafe (#pin-write target ({full} value))) (#return ()))
      (#fn read-owner (: task (#pin-ref Work-frame)) Owner
        (#return (#deref (#pin-get-payload (#pin-borrow (#get task {field})) {full} 0))))",
        guards
    );
    let replacement = "(#call replace-owner (: task (#pin-borrow-mut frame) : value
      (#struct-literal Owner (: payload (#struct-literal Payload (: left 41u64 : right 5u64))))))
      (#let restored Owner (#call read-owner (: task (#pin-borrow frame))))
      (#assert (#u64.== (#get (#get restored payload) left) 41u64))
      (#forget frame)
      (#let-mut cancelled Work-frame (#call work (: owner (#struct-literal Owner
        (: payload (#struct-literal Payload (: left 10u64 : right 7u64)))))))
      (#let first-cancel Work-poll-result (#call work-poll
        (: task (#pin-borrow-mut cancelled) : waker (#borrow waker))))
      (#let-else (work-pending cancel-pin) Work-poll-result first-cancel (#unreachable))
      (#block
        (#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task cancel-pin)))
        (#match (#get cleanup await-0)
          (#case Work-frame-cleanup-await-0-empty ())
          (#case (Work-frame-cleanup-await-0-full child) (#call cancel-child (: task child))))
        (#forget cleanup) ())
      (#call replace-owner (: task (#pin-borrow-mut cancelled) : value
        (#struct-literal Owner (: payload (#struct-literal Payload (: left 11u64 : right 7u64))))))
      (#let cancelled-value Owner (#call read-owner (: task (#pin-borrow cancelled))))
      (#let cancelled-left #u64 (#get (#get cancelled-value payload) left))
      (#forget cancelled) (#return (#u64.+.wrap answer cancelled-left))";
    let ordinary = format!(
        "{helpers}\n{}",
        standalone.replace("(#forget frame) (#return answer)", replacement)
    );
    let assembly = lim::compile_source_to_assembly(
        &ordinary,
        &path,
        &lim::CompileConfig::default(),
        &scratch.path().join("ordinary-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| {
        panic!(
            "{}",
            lim::render_diagnostic(&error, &ordinary, "ordinary.lim")
        )
    });
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(58), "{status:?} {stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());

    let unguarded = helpers
        .replace(&guards, "")
        .replace("(#assert (#u32.== (#get task pc) 4294967295u32))", "");
    let conflicting = standalone.replace(
        "(#let second Work-poll-result",
        "(#call replace-owner
      (: task pending : value (#struct-literal Owner
        (: payload (#struct-literal Payload (: left 99u64 : right 5u64))))))
      (#let second Work-poll-result",
    );
    let invalid = format!("{unguarded}\n{conflicting}");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &path,
        &lim::CompileConfig::default(),
        &scratch.path().join("invalid-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("replacement must not bypass the live internal pinned loans");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(
        error.message.contains("stored internal reference"),
        "{error:?}"
    );
    let span = error.span.expect("the actual receiver must be underlined");
    assert_eq!(&invalid[span.start..span.end], "pending");
    assert!(
        error
            .labels
            .iter()
            .any(|label| invalid[label.span.start..label.span.end].contains("#pin-write")),
        "{error:?}"
    );
}

#[test]
fn requested_parameter_access_is_public_cached_and_independently_checked() {
    let prefix = include_str!("../examples/async_fn_self_reference.lim")
        .split("(#fn main")
        .next()
        .unwrap()
        .replace("read-after-await", "work")
        .replace("Read-after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait")
        .replace(": access (: owner work-owner)", "")
        .replace(
            ": protocol WorkAwait",
            ": protocol WorkAwait : access (: owner work-owner)",
        );
    let source = format!("{prefix}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut frame Work-frame (#call work (: owner (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 40u64 : right 5u64)))))))
        (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let answer #u64 (#match second (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#call work-owner-replace (: task (#pin-borrow-mut frame) : value (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 41u64 : right 5u64))))))
        (#let completed-owner Owner (#call work-owner-read (: task (#pin-borrow frame))))
        (#assert (#u64.== (#get (#get completed-owner payload) left) 41u64))
        (#forget frame)
        (#let-mut cancelled Work-frame (#call work (: owner (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 10u64 : right 7u64)))))))
        (#let cancel-first Work-poll-result (#call work-poll (: task (#pin-borrow-mut cancelled) : waker (#borrow waker))))
        (#let-else (work-pending cancel-pin) Work-poll-result cancel-first (#unreachable))
        (#block
          (#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task cancel-pin)))
          (#match (#get cleanup await-0) (#case Work-frame-cleanup-await-0-empty ())
            (#case (Work-frame-cleanup-await-0-full child) (#call cancel-child (: task child))))
          (#forget cleanup) ())
        (#call work-owner-replace (: task (#pin-borrow-mut cancelled) : value (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 11u64 : right 7u64))))))
        (#let cancelled-owner Owner (#call work-owner-read (: task (#pin-borrow cancelled))))
        (#let cancelled-left #u64 (#get (#get cancelled-owner payload) left))
        (#forget cancelled) (#return (#u64.+.wrap answer cancelled-left)))");
    let scratch = support::Scratch::new("async-public-parameter-access");
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let mut previous = None;
    for _ in 0..2 {
        let assembly = lim::compile_source_to_assembly(
            &source,
            &path,
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, &source, "input.lim")));
        let binary = scratch.path().join("program");
        lim::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let (status, stdout, stderr) =
            support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
        assert_eq!(status.code(), Some(58), "{status:?} {stderr:?}");
        assert!(stdout.is_empty() && stderr.is_empty());
        lim::write_generated_sources_from_path_with_config_and_cache(
            &source, &path, &output, &config, &cache,
        )
        .unwrap();
        let artifact = fs::read_dir(&output)
            .unwrap()
            .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
            .find(|text| text.contains("(#fn work-poll "))
            .unwrap();
        assert!(artifact.contains("(#fn work-owner-read "));
        assert!(artifact.contains("(#fn work-owner-replace "));
        if let Some(previous) = previous.replace(artifact.clone()) {
            assert_eq!(artifact, previous);
        }
    }
    let artifact = previous.unwrap();
    let invocation = lim::parse(&source)
        .unwrap()
        .into_iter()
        .find(|node| source[node.span.start..node.span.end].starts_with("(@#async-fn-pinned"))
        .unwrap();
    let standalone = format!(
        "{}\n{artifact}\n{}",
        &source[..invocation.span.start],
        &source[invocation.span.end..]
    );
    let assembly = lim::compile_source_to_assembly(
        &standalone,
        &path,
        &lim::CompileConfig::default(),
        &scratch.path().join("ordinary-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = scratch.path().join("ordinary");
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
    assert_eq!(status.code(), Some(58), "{status:?} {stderr:?}");
}

#[test]
fn parameter_access_rejects_invalid_requests_without_publishing_generated_code() {
    let scratch = support::Scratch::new("async-access-invalid");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    for (index, (context, kind, parameters, access, suffix, expected)) in [
        (
            "",
            "#async-fn-pinned",
            "(: amount #u64)",
            "(missing work-amount)",
            "",
            "unknown parameter 'missing'",
        ),
        (
            "",
            "#async-fn-pinned",
            "(: amount #u64)",
            "(amount work-amount) (amount other)",
            "",
            "repeats parameter",
        ),
        (
            "(#struct Token (: amount #u64)) (#linear Token)",
            "#async-fn-pinned",
            "(: amount Token)",
            "(amount work-amount)",
            "",
            "reference-free Copy",
        ),
        (
            "",
            "#async-fn-pinned",
            "(: amount (#ref #u64))",
            "(amount work-amount)",
            "",
            "reference-free Copy",
        ),
        (
            "(#struct Holder (: value (#ref #u64)))",
            "#async-fn-pinned",
            "(: amount Holder)",
            "(amount work-amount)",
            "",
            "reference-free Copy",
        ),
        (
            "",
            "#async-fn-pinned",
            "(: amount (#ref-mut #u64))",
            "(amount work-amount)",
            "",
            "reference-free Copy",
        ),
        (
            "",
            "#async-fn",
            "(: amount #u64)",
            "(amount work-amount)",
            "",
            "requires @#async-fn-pinned",
        ),
        (
            "",
            "#async-fn-pinned",
            "(: amount #u64)",
            "(amount work-amount)",
            "(#fn work-amount-read () #u64 (#return 0u64))",
            "conflicts with an existing declaration",
        ),
        (
            "",
            "#async-fn-pinned",
            "(: amount #u64)",
            "(amount work-amount)",
            "(#fn work-amount-replace () () (#return ()))",
            "conflicts with an existing declaration",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!(
            "{context} (@{kind} (: protocol WorkAwait : waker #u64 : access ({access})
          : function (#fn work {parameters} #u64 (#forget amount) (#return 42u64))))
          {suffix} (#fn main () #u64 (#return 0u64))"
        );
        let cache = scratch.path().join(format!("cache-{index}"));
        let output = scratch.path().join(format!("output-{index}"));
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.message.contains(expected), "{index}: {error:?}");
        assert!(error.span.is_some(), "{index}: {error:?}");
        let error = lim::write_generated_sources_from_path_with_config_and_cache(
            &source,
            &scratch.path().join("input.lim"),
            &output,
            &config,
            &cache,
        )
        .unwrap_err();
        assert!(error.contains(expected), "{index}: {error:?}");
        assert!(
            !output.exists() || fs::read_dir(&output).unwrap().next().is_none(),
            "invalid request was published"
        );
    }
}

#[test]
fn access_handles_unit_aliases_multiple_parameters_and_imports() {
    for (import, prefix, frame) in [
        ("#import", "", "Work-frame"),
        ("#import-external", "Ext-", "Ext-work-frame"),
    ] {
        let scratch = support::Scratch::new("async-access-import");
        let library = "(#type Amount #u64) (#type Nothing ())
          (@#async-fn-pinned (: protocol WorkAwait : waker #u64
            : access (: empty unit-access : amount amount-access : other other-access)
            : function (#fn work (: empty Nothing : amount Amount : other #u64) #u64
              (#return amount))))";
        // Test fixture data, not a workspace source edit.
        fs::write(scratch.path().join("library.lim"), library).unwrap();
        let source = format!("({import} \"library.lim\" {prefix})
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let-mut frame {frame} (#call {prefix}work (: {prefix}empty () : {prefix}amount 40u64 : {prefix}other 5u64)))
            (#let poll-result #u64 (#match
              (#call {prefix}work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker)))
              (#case ({prefix}work-ready answer) answer)
              (#case ({prefix}work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
            (#assert (#u64.== poll-result 40u64))
            (#call {prefix}unit-access-replace (: task (#pin-borrow-mut frame) : value ()))
            (#let empty {prefix}Nothing (#call {prefix}unit-access-read (: task (#pin-borrow frame))))
            (#call {prefix}amount-access-replace (: task (#pin-borrow-mut frame) : value 42u64))
            (#call {prefix}other-access-replace (: task (#pin-borrow-mut frame) : value 7u64))
            (#let other #u64 (#call {prefix}other-access-read (: task (#pin-borrow frame))))
            (#assert (#u64.== other 7u64))
            (#let answer {prefix}Amount (#call {prefix}amount-access-read (: task (#pin-borrow frame))))
            (#forget frame) (#return answer))");
        let mut config = lim::CompileConfig::default();
        config.set("async-lowering", "graph");
        let assembly = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("main.lim"),
            &config,
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, &source, "main.lim")));
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
        assert_eq!(status.code(), Some(42), "{status:?} {stderr:?}");
    }
}

#[test]
fn access_traps_before_terminal_even_when_no_internal_reference_is_retained() {
    use std::os::unix::process::ExitStatusExt;
    for pending in [false, true] {
        for replace in [false, true] {
            let prefix = "(#enum Child ((Waiting #u64))) (#linear Child)
              (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
              (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
                (#return (#match task (#case (Waiting count)
                  (#if (#u64.== count 0u64) (ChildPending (Waiting 1u64)) (ChildReady 42u64))))))
              (@#async-fn-pinned (: protocol WorkAwait : waker #u64 : access (: amount amount-access)
                : function (#fn work (: amount #u64) #u64
                  (#return (#await Child ChildPending ChildReady child-poll (Waiting 0u64))))))";
            let suspend = if pending {
                "(#let first Work-poll-result (#call work-poll
              (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
              (#let-else (work-pending handle) Work-poll-result first (#unreachable))
              (#forget handle)"
            } else {
                ""
            };
            let call = if replace {
                "(#call amount-access-replace (: task (#pin-borrow-mut frame) : value 99u64))"
            } else {
                "(#let ignored #u64 (#call amount-access-read (: task (#pin-borrow frame))))"
            };
            let source = format!(
                "{prefix} (#fn main () #u64 (#let waker #u64 0u64)
              (#let-mut frame Work-frame (#call work (: amount 40u64)))
              {suspend} {call} (#forget frame) (#return 0u64))"
            );
            let scratch = support::Scratch::new("async-access-before-terminal");
            let mut config = lim::CompileConfig::default();
            config.set("async-lowering", "graph");
            let assembly = lim::compile_source_to_assembly(
                &source,
                &scratch.path().join("main.lim"),
                &config,
                &scratch.path().join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
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
            assert_eq!(
                status.signal(),
                Some(4),
                "pending={pending} replace={replace}: {status:?} {stderr:?}"
            );
        }
    }
}
