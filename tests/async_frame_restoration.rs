mod support;

use std::{fs, process::Command, time::Duration};

// Prove the ordinary-code boundary before choosing a public naming/interface
// contract. No async-specific ownership permission is used by these helpers.
#[test]
fn finalized_frame_copy_parameter_can_be_replaced_in_the_same_storage() {
    use std::os::unix::process::ExitStatusExt;
    let prefix = include_str!("../examples/async_fn_self_reference.lim")
        .split("(#fn main")
        .next()
        .unwrap()
        .replace("read-after-await", "work")
        .replace("Read::after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait");
    let source = format!("{prefix}
      (#fn main () #u64 (#let waker #u64 0u64)
        (#let-mut frame Work::Frame (#call work (: owner (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 40u64 : right 5u64)))))))
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
        (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
        (#let answer #u64 (#match second (#case (Work::Poll.Ready result) result)
          (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
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
        .find(|text| text.contains("(#fn Work::poll "))
        .unwrap();
    assert!(artifact.contains("(#fn work-owner-read "));
    assert!(artifact.contains("(#fn work-owner-replace "));
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
        .find(|text| text.contains("(#fn Work::poll "))
        .unwrap();
    assert_eq!(warm_artifact, artifact);
    let invocation = lim::parse(&source)
        .unwrap()
        .into_iter()
        .find(|node| {
            source[node.span.start..node.span.end].starts_with("(#generate #async-fn-pinned")
        })
        .unwrap();
    let standalone = format!(
        "{}\n{artifact}\n{}",
        &source[..invocation.span.start],
        &source[invocation.span.end..]
    );
    let program = lim::parse_program(&standalone).unwrap();
    lim::check_types(&program).unwrap();
    // Exercise the actual ordinary word-backed implementation, not an invented
    // Empty/Full cell layout. Rename copies to prove they need no async-aware
    // native checking or compiler-generated naming convention.
    let declarations = lim::parse(&artifact).unwrap();
    let helper = |name: &str, renamed: &str| {
        let declaration = declarations
            .iter()
            .find(|node| {
                matches!(&node.expr, lim::Expr::List(items)
                if matches!(items.get(1), Some(lim::Expr::Symbol(value)) if value == name))
            })
            .unwrap();
        artifact[declaration.span.start..declaration.span.end].replacen(
            &format!("(#fn {name} "),
            &format!("(#fn {renamed} "),
            1,
        )
    };
    let helpers = format!(
        "{}\n{}",
        helper("work-owner-replace", "replace-owner"),
        helper("work-owner-read", "read-owner")
    );
    assert!(helpers.contains("#word-write"));
    assert!(helpers.contains("#word-read"));
    assert!(!helpers.contains("#variant-is"));
    let replacement = "(#call replace-owner (: task (#pin-borrow-mut frame) : value
      (#struct-literal Owner (: payload (#struct-literal Payload (: left 41u64 : right 5u64))))))
      (#let restored Owner (#call read-owner (: task (#pin-borrow frame))))
      (#assert (#u64::eq (#get (#get restored payload) left) 41u64))
      (#forget frame)
      (#let-mut cancelled Work::Frame (#call work (: owner (#struct-literal Owner
        (: payload (#struct-literal Payload (: left 10u64 : right 7u64)))))))
      (#let first-cancel Work::Poll (#call Work::poll
        (: task (#pin-borrow-mut cancelled) : waker (#borrow waker))))
      (#let-else (Work::Poll.Pending cancel-pin) Work::Poll first-cancel (#unreachable))
      (#block
        (#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup (: task cancel-pin)))
        (#match (#get cleanup await-0)
          (#case Work::Frame::Cleanup::Await-0.Empty ())
          (#case (Work::Frame::Cleanup::Await-0.Full child) (#call cancel-child (: task child))))
        (#forget cleanup) ())
      (#call replace-owner (: task (#pin-borrow-mut cancelled) : value
        (#struct-literal Owner (: payload (#struct-literal Payload (: left 11u64 : right 7u64))))))
      (#let cancelled-value Owner (#call read-owner (: task (#pin-borrow cancelled))))
      (#let cancelled-left #u64 (#get (#get cancelled-value payload) left))
      (#forget cancelled) (#return (#u64::add-wrap answer cancelled-left))";
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

    let conflicting = standalone.replace(
        "(#let second Work::Poll",
        "(#call replace-owner
      (: task pending : value (#struct-literal Owner
        (: payload (#struct-literal Payload (: left 99u64 : right 5u64))))))
      (#let second Work::Poll",
    );
    let invalid = format!("{helpers}\n{conflicting}");
    let assembly = lim::compile_source_to_assembly(
        &invalid,
        &path,
        &lim::CompileConfig::default(),
        &scratch.path().join("invalid-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = scratch.path().join("pending-replacement");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, _) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    // Raw word storage has no native reference-bearing type. Its unsafe
    // implementation must retain the explicit terminal-state guard; pinning
    // alone does not authorize overwriting live self-reference targets.
    assert_eq!(
        status.signal(),
        Some(4),
        "replacement while Pending must trap at its state guard: {status:?}"
    );
}

#[test]
fn requested_parameter_access_is_public_cached_and_independently_checked() {
    let prefix = include_str!("../examples/async_fn_self_reference.lim")
        .split("(#fn main")
        .next()
        .unwrap()
        .replace("read-after-await", "work")
        .replace("Read::after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait")
        .replace(": access (: owner work-owner)", "")
        .replace(
            ": protocol WorkAwait",
            ": protocol WorkAwait : access (: owner work-owner)",
        );
    let source = format!("{prefix}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut frame Work::Frame (#call work (: owner (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 40u64 : right 5u64)))))))
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
        (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
        (#let answer #u64 (#match second (#case (Work::Poll.Ready value) value)
          (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#call work-owner-replace (: task (#pin-borrow-mut frame) : value (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 41u64 : right 5u64))))))
        (#let completed-owner Owner (#call work-owner-read (: task (#pin-borrow frame))))
        (#assert (#u64::eq (#get (#get completed-owner payload) left) 41u64))
        (#forget frame)
        (#let-mut cancelled Work::Frame (#call work (: owner (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 10u64 : right 7u64)))))))
        (#let cancel-first Work::Poll (#call Work::poll (: task (#pin-borrow-mut cancelled) : waker (#borrow waker))))
        (#let-else (Work::Poll.Pending cancel-pin) Work::Poll cancel-first (#unreachable))
        (#block
          (#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup (: task cancel-pin)))
          (#match (#get cleanup await-0) (#case Work::Frame::Cleanup::Await-0.Empty ())
            (#case (Work::Frame::Cleanup::Await-0.Full child) (#call cancel-child (: task child))))
          (#forget cleanup) ())
        (#call work-owner-replace (: task (#pin-borrow-mut cancelled) : value (#struct-literal Owner
          (: payload (#struct-literal Payload (: left 11u64 : right 7u64))))))
        (#let cancelled-owner Owner (#call work-owner-read (: task (#pin-borrow cancelled))))
        (#let cancelled-left #u64 (#get (#get cancelled-owner payload) left))
        (#forget cancelled) (#return (#u64::add-wrap answer cancelled-left)))");
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
            .find(|text| text.contains("(#fn Work::poll "))
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
        .find(|node| {
            source[node.span.start..node.span.end].starts_with("(#generate #async-fn-pinned")
        })
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
            "(#struct Token (#linear) (: amount #u64)) ",
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
            "(#struct Holder () (: value (#ref #u64)))",
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
            "requires #generate #async-fn-pinned",
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
            "{context} (#generate {kind} (: protocol WorkAwait : waker #u64 : access ({access})
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
        ("#import", "", "Work::Frame"),
        ("#import-external", "Ext-", "Ext-Work::Frame"),
    ] {
        let scratch = support::Scratch::new("async-access-import");
        let library = "(#type Amount #u64) (#type Nothing ())
          (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
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
              (#call {prefix}Work::poll (: task (#pin-borrow-mut frame) : waker (#borrow waker)))
              (#case ({prefix}Work::Ready answer) answer)
              (#case ({prefix}Work::Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
            (#assert (#u64::eq poll-result 40u64))
            (#call {prefix}unit-access-replace (: task (#pin-borrow-mut frame) : value ()))
            (#let empty {prefix}Nothing (#call {prefix}unit-access-read (: task (#pin-borrow frame))))
            (#call {prefix}amount-access-replace (: task (#pin-borrow-mut frame) : value 42u64))
            (#call {prefix}other-access-replace (: task (#pin-borrow-mut frame) : value 7u64))
            (#let other #u64 (#call {prefix}other-access-read (: task (#pin-borrow frame))))
            (#assert (#u64::eq other 7u64))
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
            let prefix = "(#enum Child (#linear) ((Child.Waiting #u64)))
              (#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64)))
              (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
                (#return (#match task (#case (Child.Waiting count)
                  (#if (#u64::eq count 0u64) (ChildPoll.ChildPending (Child.Waiting 1u64)) (ChildPoll.ChildReady 42u64))))))
              (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 : access (: amount amount-access)
                : function (#fn work (: amount #u64) #u64
                  (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))))))";
            let suspend = if pending {
                "(#let first Work::Poll (#call Work::poll
              (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
              (#let-else (Work::Poll.Pending handle) Work::Poll first (#unreachable))
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
              (#let-mut frame Work::Frame (#call work (: amount 40u64)))
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
