mod support;

use std::{fs, process::Command, time::Duration};

// Prove the ordinary-code boundary before choosing a public naming/interface
// contract. No async-specific ownership permission is used by these helpers.
#[test]
fn finalized_frame_copy_parameter_can_be_replaced_in_the_same_storage() {
    let prefix = include_str!("../examples/async_fn_self_reference.lim")
        .split("(#fn cancel-self-ref-state")
        .next()
        .unwrap()
        .replace("read-after-await", "work")
        .replace("Read-after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait");
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
