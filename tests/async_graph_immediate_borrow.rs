//! Operation-local and retired poll-local references in movable async frames.
#[path = "support/generated_source.rs"]
mod generated_source;
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
    run_with_role(source, expected_stdout, "immediate-owner-project")
}

fn run_with_role(source: &str, expected_stdout: &[u8], role: &str) {
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
            .find(|text| text.contains("#fn Work::poll "))
            .unwrap();
        // Contiguous word-backed owners are projected inline rather than
        // through the older typed-cell helper. The checks and native execution
        // below verify both representations, including cached independent code.
        assert!(
            artifact.contains(role)
                || (artifact.contains("#word-view") && artifact.contains("#borrow-slice")),
            "neither {role} nor an inline word-backed projection was emitted"
        );
        let invocation = lim::parse_source_unit(source)
            .unwrap()
            .into_iter()
            .find(|node| {
                matches!(&node.expr, lim::Expr::List(items)
                if matches!(items.first(), Some(lim::Expr::Generate))
                && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == "#async-fn"))
            })
            .unwrap();
        let standalone = format!(
            "{}\n{}\n{}",
            &source[..invocation.span.start],
            generated_source::ordinary_source(&artifact),
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
fn stored_local_handles_are_retired_before_moving_a_pending_frame() {
    for body in [
        "(#let-mut counter Counter (#struct-literal Counter ((value 40u64))))
          (#let container (#ref-mut Counter) (#borrow-mut counter))
          (#call touch ((target (#borrow-mut (#get container value)))))
          (#call touch ((target (#borrow-mut (#get container value)))))
          (#forget container)
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#let answer #u64 (#get counter value)) (#forget counter) (#return answer)",
        "(#let left #u64 40u64) (#let right #u64 50u64)
          (#let view (#ref #u64) (#if choose (#borrow left) (#borrow right)))
          (#let answer #u64 (#deref view)) (#forget view)
          (#assert (#u64::eq answer (#if choose 40u64 50u64)))
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#return 42u64)",
        "(#let left Wide (#struct-literal Wide ((padding 7u8) (value 40u128))))
          (#let right (#array #u128 2) (#array-of (#array #u128 2) 1u128 50u128))
          (#let view (#ref #u128)
            (#if choose (#borrow (#get left value)) (#borrow (#index right 1usize))))
          (#let answer #u128 (#deref view)) (#forget view)
          (#assert (#u128::eq answer (#if choose 40u128 50u128)))
          (#forget left) (#forget right)
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#return 42u64)",
        "(#let-mut left #u64 40u64)
          (#let-mut right Counter (#struct-literal Counter ((value 50u64))))
          (#let view (#ref-mut #u64)
            (#if choose (#borrow-mut left) (#borrow-mut (#get right value))))
          (#deref-set view (#u64::add-wrap (#deref view) 2u64))
          (#let answer #u64 (#deref view)) (#forget view)
          (#assert (#u64::eq answer (#if choose 42u64 52u64)))
          (#assert (#u64::eq left (#if choose 42u64 40u64)))
          (#assert (#u64::eq (#get right value) (#if choose 50u64 52u64)))
          (#forget right)
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#return 42u64)",
        "(#let left Wide (#struct-literal Wide ((padding 7u8) (value 40u128))))
          (#let right (#array #u128 2) (#array-of (#array #u128 2) 1u128 50u128))
          (#let-mut index #usize 1usize)
          (#let view (#ref #u128)
            (#if choose (#borrow (#get left value)) (#borrow (#index right index))))
          (#set index 0usize)
          (#let answer #u128 (#deref view)) (#forget view)
          (#assert (#u128::eq answer (#if choose 40u128 50u128)))
          (#forget left) (#forget right)
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#return 42u64)",
        "(#let-mut items (#array Counter 2)
            (#array-of (#array Counter 2)
              (#struct-literal Counter ((value 20u64)))
              (#struct-literal Counter ((value 20u64)))))
          (#let-mut index #usize 1usize)
          (#call touch ((target (#borrow-mut (#get (#index items index) value)))))
          (#set index 0usize)
          (#call touch ((target (#borrow-mut (#get (#index items index) value)))))
          (#let answer #u64
            (#u64::add-wrap (#get (#index items 0usize) value) (#get (#index items 1usize) value)))
          (#forget items)
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#return answer)",
        "(#let owner #u64 40u64)
          (#let answer #u64 (#borrow owner (#u64::add-wrap owner 2u64)))
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
          (#return answer)",
    ] {
        for choose in [false, true] {
            let source = format!(
                "#struct Counter () ((value #u64))
#struct Wide () ((padding #u8) (value #u128))
#fn touch {{
  #params = ((target (#ref-mut #u64)));
  #returns = ();
  #body = (
                    (#deref-set target (#u64::add-wrap (#deref target) 1u64)) (#return ())
  );
}}
#enum Child (#linear) (Child.Start Child.Resume)
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {{
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
                    (#return (#match task (#case Child.Start (ChildPoll.ChildPending Child.Resume))
                      (#case Child.Resume (ChildPoll.ChildReady 0u64))))
  );
}}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
                    (function (#fn work ((choose #bool)) #u64 {body})))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                    (#let waker #u64 0u64)
                    (#let first Work::Poll (#call Work::poll
                      ((task (#call work ((choose {choose})))) (waker (#borrow waker)))))
                    (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
                    (#return (#match (#call Work::poll ((task task) (waker (#borrow waker))))
                      (#case (Work::Poll.Ready answer) answer)
                      (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}}\n"
            );
            run_with_role(&source, &[], "owner-project");
        }
    }
    run_with_role(
        include_str!("../examples/async_fn_poll_local_borrow.lim"),
        &[],
        "owner-project",
    );
}

fn whole_array_element_source() -> &'static str {
    "#struct Counter (#linear) ((value #u64))
#fn touch-counter {
  #params = ((target (#ref-mut Counter)));
  #returns = ();
  #body = (
          (#deref-set (#borrow-mut (#get target value))
            (#u64::add-wrap (#get target value) 1u64))
          (#return ())
  );
}
#enum Child (#linear) (Child.Start Child.Resume)
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case Child.Start (ChildPoll.ChildPending Child.Resume))
            (#case Child.Resume (ChildPoll.ChildReady 0u64))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work () #u64
            (#let-mut items (#array Counter 2)
              (#array-of (#array Counter 2)
                (#struct-literal Counter ((value 20u64)))
                (#struct-literal Counter ((value 20u64)))))
            (#let-mut index #usize 1usize)
            (#let view (#ref-mut Counter) (#borrow-mut (#index items index)))
            (#set index 0usize)
            (#call touch-counter ((target view)))
            (#let second (#ref-mut Counter) (#borrow-mut (#index items index)))
            (#call touch-counter ((target second)))
            (#let answer #u64
              (#u64::add-wrap (#get (#index items 0usize) value) (#get (#index items 1usize) value)))
            (#forget items)
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))
            (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#return (#match (#call Work::poll ((task task) (waker (#borrow waker))))
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}\n"
}

#[test]
fn whole_array_element_borrows_end_before_suspension() {
    for source in [
        whole_array_element_source().to_owned(),
        whole_array_element_source().replace("#struct Counter (#linear)", "#struct Counter ()"),
    ] {
        run_with_role(&source, &[], "owner-project-array");
    }
}

#[test]
fn whole_array_element_storage_preserves_source_and_boundary_checks() {
    for (needle, replacement, expected) in [
        ("(#set index 0usize)", "(#forget items)", "borrow"),
        (
            "(#set index 0usize)",
            "(#let overlap (#ref Counter) (#borrow (#index items 0usize))) (#forget overlap)",
            "borrow",
        ),
        (
            "(#set index 0usize)",
            "(#let early #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Start))",
            "pinned async frame",
        ),
    ] {
        let mut source = whole_array_element_source().replace(needle, replacement);
        if replacement == "(#forget items)" {
            // Do not mask the live-borrow violation with a later double move.
            let start = source.find("(#let second").unwrap();
            let end = source.find("(#return answer)").unwrap() + "(#return answer)".len();
            source.replace_range(start..end, "(#return 42u64)");
        }
        let scratch = support::Scratch::new("async-whole-element-invalid");
        let cache = scratch.path().join("cache");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.message.contains(expected), "{error:?}");
        let span = error.span.expect("invalid borrow must identify source");
        assert!(
            span.start < span.end && span.end <= source.len(),
            "{error:?}"
        );
        let offending_line = source.lines().nth(span.line - 1).unwrap();
        assert!(
            offending_line.contains(if expected == "pinned async frame" {
                "#borrow-mut (#index items index)"
            } else {
                replacement
            }),
            "{error:?}"
        );
        if expected == "borrow" {
            assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        }
        assert!(
            !cache.exists(),
            "invalid source must not publish generated code"
        );
    }
}

#[test]
fn poll_local_pointer_storage_does_not_authorize_source_aliasing() {
    for body in [
        "(#let-mut owner #u64 40u64)
          (#let view (#ref #u64) (#borrow owner))
          (#set owner 42u64) (#return (#deref view))",
        "(#let-mut owner #u64 40u64)
          (#let view (#ref-mut #u64) (#borrow-mut owner))
          (#let alias (#ref #u64) (#borrow owner))
          (#let answer #u64 (#deref view)) (#forget alias) (#forget view)
          (#return answer)",
        "(#let-mut owner #u64 40u64) (#let-mut other #u64 50u64)
          (#let view (#ref #u64) (#if choose (#borrow owner) (#borrow other)))
          (#set owner 42u64) (#return (#deref view))",
        "(#let-mut owner #u64 40u64) (#let-mut other #u64 50u64)
          (#let view (#ref-mut #u64) (#if choose (#borrow-mut owner) (#borrow-mut other)))
          (#let alias (#ref #u64) (#borrow owner))
          (#let answer #u64 (#deref view)) (#forget alias) (#forget view)
          (#return answer)",
    ] {
        let source = format!(
            "#generate #async-fn ((protocol WorkAwait) (waker #u64)
                (function (#fn work ((choose #bool)) #u64 {body})))\n"
        );
        let scratch = support::Scratch::new("async-poll-local-alias");
        let cache = scratch.path().join("cache");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        let span = error
            .span
            .expect("aliasing must identify the source access");
        assert_eq!(
            &source[span.start..span.end],
            if body.contains("#set") {
                "#set"
            } else {
                "#borrow"
            }
        );
        let needle = if body.contains("#set") {
            "#set owner 42u64"
        } else {
            "#borrow owner))\n          (#let answer"
        };
        assert_eq!(span.start, source.find(needle).unwrap(), "{error:?}");
        assert!(
            !cache.exists(),
            "invalid source must not publish generated code"
        );
    }
}

#[test]
fn shared_array_slice_and_range_borrow_actual_local_storage() {
    let source = r#"
#fn sum {
  #params = ((items (#slice #u64)));
  #returns = #u64;
  #body = (
          (#return (#u64::add-wrap (#deref (#slice-idx items 0usize))
            (#deref (#slice-idx items 1usize))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work () #u64
            (#let values (#array #u64 3) (#array-of (#array #u64 3) 1u64 20u64 22u64))
            (#return (#call sum ((items (#borrow-slice values 1usize 3usize))))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#return (#match (#call Work::poll ((task (#call work ())) (waker (#borrow waker))))
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
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
#fn bound {
  #params = ((value #usize));
  #returns = #usize;
  #body = (
          (#let byte #u8 120u8)
          (#let pointer #usize (#ptr-address (#ref-ptr (#borrow byte))))
          (#assert (#i64::eq (#unsafe (#linux-syscall #i64 1usize (1usize pointer 1usize))) 1i64))
          (#return value)
  );
}
#fn sum {
  #params = ((items (#slice #u64)));
  #returns = #u64;
  #body = (
          (#return (#u64::add-wrap (#deref (#slice-idx items 0usize))
            (#deref (#slice-idx items 1usize))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work () #u64
            (#let values (#array #u64 2) (#array-of (#array #u64 2) 20u64 22u64))
            (#let answer #u64 (#call sum ((items (#borrow-slice values
              (#call bound ((value 0usize)))
              (#call bound ((value 2usize))))))))
            (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#return (#match (#call Work::poll ((task (#call work ())) (waker (#borrow waker))))
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#,
        b"xx",
    );
}

#[test]
fn slices_of_reference_elements_preserve_the_elements_referents() {
    run(r#"
#fn sum {
  #params = ((items (#slice (#ref #u64))));
  #returns = #u64;
  #body = (
          (#return (#u64::add-wrap (#deref (#deref (#slice-idx items 0usize)))
            (#deref (#deref (#slice-idx items 1usize)))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((first (#ref #u64)) (second (#ref #u64))) #u64
            (#let values (#array (#ref #u64) 2)
              (#array-of (#array (#ref #u64) 2) first second))
            (#return (#call sum ((items (#borrow-slice values))))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let first #u64 40u64) (#let second #u64 2u64) (#let waker #u64 0u64)
          (#return (#match (#call Work::poll
            ((task (#call work ((first (#borrow first)) (second (#borrow second)))))
             (waker (#borrow waker))))
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#);
}

#[test]
fn slice_borrows_do_not_allow_local_escape_or_mutation_of_live_referents() {
    for body in [
        r#"#fn work {
  #params = ();
  #returns = (#slice #u64);
  #body = (
            (#let values (#array #u64 2) (#array-of (#array #u64 2) 20u64 22u64))
            (#return (#borrow-slice values))
  );
}
"#,
        r#"#fn work {
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 20u64 22u64))
            (#let items (#slice #u64) (#borrow-slice values))
            (#set values (#array-of (#array #u64 2) 1u64 2u64))
            (#return (#deref (#slice-idx items 0usize)))
  );
}
"#,
    ] {
        // The ordinary source must fail ownership checking independently of
        // any earlier unsupported-address rejection in graph preparation.
        let ordinary = lim::parse_program(body).unwrap();
        let ordinary_error = lim::check_types(&ordinary).unwrap_err();
        assert!(
            ordinary_error.contains("reference to local") || ordinary_error.contains("borrow"),
            "{ordinary_error}"
        );
        let source =
            format!("#generate #async-fn ((protocol WorkAwait) (waker #u64) (function ({body})))\n");
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
#struct Token (#linear) ((value #u64))

#fn inspect {
  #params = ((items (#slice Token)));
  #returns = #u64;
  #body = (
          (#return (#get (#slice-idx items 0usize) value))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work () #u64
            (#let values (#array Token 1)
              (#array-of (#array Token 1) (#struct-literal Token ((value 42u64)))))
            (#let answer #u64 (#call inspect ((items (#borrow-slice values)))))
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
        error.message.contains("Non-Copy array slice borrowing"),
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

const PAIR_SOURCE: &str = "#struct Pair () ((left #u64) (right #u64))
#fn touch {
  #params = ((left (#ref-mut #u64)) (right (#ref-mut #u64)));
  #returns = ();
  #body = (
      (#deref-set left 20u64) (#deref-set right 22u64) (#return ())
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function (#fn work () #u64
      (#let-mut pair Pair (#struct-literal Pair ((left 0u64) (right 0u64))))
      (#call touch ((left (#borrow-mut (#get pair left))) (right (#borrow-mut (#get pair right)))))
      (#return (#u64::add-wrap (#get pair left) (#get pair right))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let waker #u64 0u64)
      (#return (#match (#call Work::poll ((task (#call work ())) (waker (#borrow waker))))
        (#case (Work::Poll.Ready value) value)
        (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}\n";

#[test]
fn one_synchronous_call_borrows_disjoint_struct_fields() {
    run(PAIR_SOURCE);
}

#[test]
fn immediate_emission_does_not_authorize_aliasing() {
    let source = PAIR_SOURCE.replace(
        "(right (#borrow-mut (#get pair right)))",
        "(right (#borrow-mut (#get pair left)))",
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
