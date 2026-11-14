mod support;

use std::{process::Command, time::Duration};

fn run(source: &str) -> String {
    let scratch = support::Scratch::new("call-graph");
    // Import IO after the fixture to preserve its explicitly asserted lines.
    let program = lim::parse_program(&format!(
        "{source}\n(#std)
      (#fn print-trace ((text (#slice #char))) ()
        (#let owned String (#match (#call String::from-chars (($ text)))
          (#case (StringCreateResult.StringCreated string) string)
          (#case (StringCreateResult.StringCreateFailed error) (#panic))))
        (#let status #i64 (#println (#borrow owned)))
        (#call String::free ((string owned)))
        (#return ()))\n"
    ))
    .unwrap();
    lim::check_types(&program).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
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
        support::run(&mut Command::new(binary), Duration::from_secs(5), 8192).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stderr.is_empty(), "{stderr:?}");
    String::from_utf8(stdout).unwrap()
}

#[test]
fn executing_lines_distinguish_repeated_calls() {
    let source = "(#fn third () ()
  (#call print-trace ((text (#call-graph))))
  (#return ()))
(#fn second () ()
  (#call third ())
  (#return ()))
(#fn main () #u64
  (#call second ())
  (#call second ())
  (#return 42u64))";
    assert_eq!(
        run(source),
        "main:8 -> second:5 -> third:2\nmain:9 -> second:5 -> third:2\n"
    );
}

#[test]
fn main_trace_and_live_distinct_trace_sites() {
    let source = "(#fn main () #u64
  (#let first (#slice #char) (#call-graph))
  (#let second (#slice #char) (#call-graph))
  (#call print-trace ((text first)))
  (#call print-trace ((text second)))
  (#return 42u64))";
    assert_eq!(run(source), "main:2\nmain:3\n");
}

#[test]
fn only_the_executed_branch_appears() {
    let source = "(#fn leaf () ()
  (#call print-trace ((text (#call-graph))))
  (#return ()))
(#fn left () ()
  (#call leaf ())
  (#return ()))
(#fn right () ()
  (#call leaf ())
  (#return ()))
(#fn choose ((condition #bool)) ()
  (#if condition (#call left ()) (#call right ()))
  (#return ()))
(#fn main () #u64
  (#call choose ((condition true)))
  (#call choose ((condition false)))
  (#return 42u64))";
    assert_eq!(
        run(source),
        "main:14 -> choose:11 -> left:5 -> leaf:2\nmain:15 -> choose:11 -> right:8 -> leaf:2\n"
    );
}

#[test]
fn implicit_clone_hooks_participate_in_the_chain() {
    let source = "(#struct Value () ((number #u64)))
(#fn Value::clone ((value Value)) Value
  (#call print-trace ((text (#call-graph))))
  (#return value))
(#fn main () #u64
  (#let value Value (#struct-literal Value ((number 42u64))))
  (#let copied Value (#clone value))
  (#return (#get copied number)))";
    assert_eq!(run(source), "main:7 -> Value::clone:3\n");
}

#[test]
fn thread_workers_receive_owned_caller_contexts() {
    let source = "(#fn worker () #u64
  (#call print-trace ((text (#call-graph))))
  (#return 42u64))
(#generate #thread-spawn ((task Task) (worker worker)))
(#fn main () #u64
  (#let-else (Task::SpawnResult.Ok running) Task::SpawnResult
    (#call Task::spawn ())
    (#panic))
  (#return (#match (#call Task::join ((task running)))
    (#case (Task::JoinResult.Ok answer) answer)
    (#case (Task::JoinResult.Error (#tuple retry error)) (#panic)))))";
    assert_eq!(run(source), "main:7 -> worker:2\n");
}

#[test]
fn async_validation_witnesses_keep_their_original_checks() {
    let source = "(#fn report () ()
  (#call print-trace ((text (#call-graph))))
  (#return ()))
(#generate #async-fn ((protocol WorkAwait) (waker #u64)
  (function (#fn work () #u64
    (#call report ())
    (#return 42u64)))))
(#fn main () #u64
  (#let waker #u64 0u64)
  (#return (#match (#call Work::poll ((task (#call work ())) (waker (#borrow waker))))
    (#case (Work::Poll.Ready value) value)
    (#case (Work::Poll.Pending pending) (#block (#forget pending) (#unreachable))))))";
    let output = run(source);
    assert!(output.starts_with("main:10 -> Work::poll:"), "{output}");
    assert!(output.ends_with(" -> report:2\n"), "{output}");
}

#[test]
fn trace_views_cannot_escape_their_stack_storage() {
    let program = lim::parse_program(
        "(#fn trace () (#slice #char) (#return (#call-graph)))
      (#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
    assert!(lim::check_types(&program).is_err());
}

#[test]
fn trace_requires_no_arguments() {
    assert!(lim::parse_program("(#fn main () #u64 (#call-graph 1u64) (#return 42u64))").is_err());
}

#[test]
fn shared_callees_do_not_expand_into_every_possible_path() {
    let mut source = "(#fn step0 () #usize (#return (#slice-len (#call-graph))))\n".to_owned();
    for index in 1..=24 {
        let child = index - 1;
        source.push_str(&format!(
            "(#fn step{index} () #usize
          (#return (#usize::add-wrap (#call step{child} ()) (#call step{child} ()))))\n"
        ));
    }
    source.push_str("(#fn main () #usize (#return (#call step24 ())))");
    let program = lim::parse_program(&source).unwrap();
    // More than sixteen million call paths still need only one append helper.
    assert_eq!(program.items.len(), 27);
}
