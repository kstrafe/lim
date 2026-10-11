//! Operation-local references do not need movable-frame reference storage.
mod support;

use std::{fs, process::Command, time::Duration};

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

fn run(source: &str) {
    run_output(source, &[])
}

fn run_output(source: &str, expected_stdout: &[u8]) {
    let scratch = support::Scratch::new("async-graph-immediate");
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    let mut previous = None;
    for _ in 0..2 {
        let assembly = lim::compile_source_with_generated_sources(
            source,
            &path,
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &output,
        )
        .unwrap_or_else(|error| {
            let line = error.span.map_or(1, |span| span.line);
            let excerpt = error
                .source_text
                .as_deref()
                .unwrap_or("")
                .lines()
                .skip(line.saturating_sub(3))
                .take(6)
                .collect::<Vec<_>>()
                .join("\n");
            panic!("{} at line {line}\n{excerpt}", error.message)
        });
        if let Some(previous) = previous.as_ref() {
            assert_eq!(&assembly, previous);
        }
        let artifact = fs::read_dir(&output)
            .unwrap()
            .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
            .find(|text| text.contains("(#fn work-poll "))
            .unwrap();
        assert!(artifact.contains("immediate-owner-project"));
        let invocation = lim::parse(source)
            .unwrap()
            .into_iter()
            .find(|node| source[node.span.start..node.span.end].starts_with("(@#async-fn"))
            .unwrap();
        let standalone = format!(
            "{}\n{artifact}\n{}",
            &source[..invocation.span.start],
            &source[invocation.span.end..]
        );
        let ordinary = lim::parse_program(&standalone).unwrap();
        lim::check_types(&ordinary).unwrap();
        let ordinary_assembly = lim::generate_assembly(&ordinary).unwrap();
        for (index, assembly) in [assembly.as_str(), ordinary_assembly.as_str()]
            .into_iter()
            .enumerate()
        {
            let binary = scratch.path().join(format!("program-{index}"));
            lim::link_native_binary(
                assembly,
                &binary,
                &[],
                &[],
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
            let (status, stdout, stderr) =
                support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
            assert_eq!(status.code(), Some(42), "{stderr:?}");
            assert_eq!(stdout, expected_stdout);
            assert!(stderr.is_empty());
        }
        previous = Some(assembly);
    }
}

#[test]
fn shared_array_slice_and_range_borrow_actual_local_storage() {
    let source = r#"
      (#fn sum (: items (#slice #u64)) #u64
        (#return (#u64.+.wrap (#deref (#slice-idx items 0usize))
          (#deref (#slice-idx items 1usize)))))
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let values (#array #u64 3) (#array-of (#array #u64 3) 1u64 20u64 22u64))
          (#return (#call sum (: items (#borrow-slice values 1usize 3usize)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#return (#match (#call work-poll (: task (#call work ()) : waker (#borrow waker)))
          (#case (work-ready answer) answer)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
    "#;
    run(source);
    run(&source
        .replace("(#array #u64 3)", "(#array #u64 2)")
        .replace("1u64 20u64 22u64", "20u64 22u64")
        .replace(
            "(#borrow-slice values 1usize 3usize)",
            "(#borrow-slice values)",
        ));
}

#[test]
fn operation_local_slice_bounds_are_evaluated_once_before_the_consumer() {
    run_output(
        r#"
      (#fn bound (: value #usize) #usize
        (#let byte #u8 120u8)
        (#let pointer #usize (#ptr-address (#ref-ptr (#borrow byte))))
        (#assert (#i64.== (#unsafe (#linux-syscall #i64 1usize (1usize pointer 1usize))) 1i64))
        (#return value))
      (#fn sum (: items (#slice #u64)) #u64
        (#return (#u64.+.wrap (#deref (#slice-idx items 0usize))
          (#deref (#slice-idx items 1usize)))))
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let values (#array #u64 2) (#array-of (#array #u64 2) 20u64 22u64))
          (#let answer #u64 (#call sum (: items (#borrow-slice values
            (#call bound (: value 0usize))
            (#call bound (: value 2usize))))))
          (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#return (#match (#call work-poll (: task (#call work ()) : waker (#borrow waker)))
          (#case (work-ready answer) answer)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
    "#,
        b"xx",
    );
}

#[test]
fn slices_of_reference_elements_preserve_the_elements_referents() {
    run(r#"
      (#fn sum (: items (#slice (#ref #u64))) #u64
        (#return (#u64.+.wrap (#deref (#deref (#slice-idx items 0usize)))
          (#deref (#deref (#slice-idx items 1usize))))))
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work (: first (#ref #u64) : second (#ref #u64)) #u64
          (#let values (#array (#ref #u64) 2)
            (#array-of (#array (#ref #u64) 2) first second))
          (#return (#call sum (: items (#borrow-slice values)))))))
      (#fn main () #u64
        (#let first #u64 40u64) (#let second #u64 2u64) (#let waker #u64 0u64)
        (#return (#match (#call work-poll
          (: task (#call work (: first (#borrow first) : second (#borrow second)))
           : waker (#borrow waker)))
          (#case (work-ready answer) answer)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
    "#);
}

#[test]
fn slice_borrows_do_not_allow_local_escape_or_mutation_of_live_referents() {
    for body in [
        r#"(#fn work () (#slice #u64)
          (#let values (#array #u64 2) (#array-of (#array #u64 2) 20u64 22u64))
          (#return (#borrow-slice values)))"#,
        r#"(#fn work () #u64
          (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 20u64 22u64))
          (#let items (#slice #u64) (#borrow-slice values))
          (#set values (#array-of (#array #u64 2) 1u64 2u64))
          (#return (#deref (#slice-idx items 0usize))))"#,
    ] {
        // The ordinary source must fail ownership checking independently of
        // any earlier unsupported-address rejection in graph preparation.
        let ordinary = lim::parse_program(body).unwrap();
        let ordinary_error = lim::check_types(&ordinary).unwrap_err();
        assert!(
            ordinary_error.contains("reference to local") || ordinary_error.contains("borrow"),
            "{ordinary_error}"
        );
        let source = format!("(@#async-fn (: protocol WorkAwait : waker #u64 : function {body}))");
        let scratch = support::Scratch::new("async-slice-rejection");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &config(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(
            error.code == lim::DiagnosticCode::Borrow
                || (error.code == lim::DiagnosticCode::Type
                    && error.message == "selected addresses require safe checked references"),
            "{}",
            error.message
        );
        assert!(error.span.is_some());
    }
}

#[test]
fn noncopy_array_slices_require_a_nonmoving_storage_lease() {
    let source = r#"
      (#struct Token ((value #u64)))
      (#linear Token)
      (#fn inspect (: items (#slice Token)) #u64
        (#return (#get (#slice-idx items 0usize) value)))
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let values (#array Token 1)
            (#array-of (#array Token 1) (#struct-literal Token ((value 42u64)))))
          (#let answer #u64 (#call inspect (: items (#borrow-slice values))))
          (#forget values)
          (#return answer))))
    "#;
    let scratch = support::Scratch::new("async-slice-linear-storage");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("non-Copy array slice borrowing"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert!(source[span.start..span.end].contains("#borrow-slice"));
}

#[test]
fn external_heap_contents_survive_owner_extraction_and_later_poll_calls() {
    run(include_str!("../examples/async_heap_reference.lim"));
}

#[test]
fn synchronous_scrutinee_can_mutate_a_movable_frame_local() {
    run(include_str!("../examples/async_while_let_body.lim"));
}

#[test]
fn effect_step_borrows_a_local_only_after_its_awaited_argument() {
    run(include_str!("../examples/async_for_effect_step.lim"));
}

#[test]
fn computed_step_retains_body_binding_through_awaits_and_continue() {
    let source = include_str!("../examples/async_for_computed_step.lim");
    run(source);
    run(&source.replace(
        "(#let body-ran #bool true)",
        "(#let body-ran #bool true) (#continue)",
    ));
}

const PAIR_SOURCE: &str = "(#struct Pair (: left #u64 : right #u64))
  (#fn touch (: left (#ref-mut #u64) : right (#ref-mut #u64)) ()
    (#deref-set left 20u64) (#deref-set right 22u64) (#return ()))
  (@#async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64
    (#let-mut pair Pair (#struct-literal Pair (: left 0u64 : right 0u64)))
    (#call touch (: left (#borrow-mut (#get pair left)) : right (#borrow-mut (#get pair right))))
    (#return (#u64.+.wrap (#get pair left) (#get pair right))))))
  (#fn main () #u64 (#let waker #u64 0u64)
    (#return (#match (#call work-poll (: task (#call work ()) : waker (#borrow waker)))
      (#case (work-ready value) value)
      (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))";

#[test]
fn one_synchronous_call_borrows_disjoint_struct_fields() {
    run(PAIR_SOURCE);
}

#[test]
fn immediate_emission_does_not_authorize_aliasing() {
    let source = PAIR_SOURCE.replace(
        ": right (#borrow-mut (#get pair right))",
        ": right (#borrow-mut (#get pair left))",
    );
    let scratch = support::Scratch::new("async-immediate-alias");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let span = error.span.expect("original source borrow diagnostic");
    assert!(source[span.start..span.end].contains("#borrow-mut"));
}
