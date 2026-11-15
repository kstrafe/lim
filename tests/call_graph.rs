mod support;

use std::{process::Command, time::Duration};

fn run(source: &str) -> String {
    let scratch = support::Scratch::new("call-graph");
    // Import IO after the fixture to preserve its explicitly asserted lines.
    let program = lim::parse_program(&format!(
        "{source}\n#std
#fn print-trace {{
  #params = ((text (#slice #char)));
  #returns = ();
  #body = (
          (#let owned String (#match (#call String::from-chars (($ text)))
            (#case (StringCreateResult.StringCreated string) string)
            (#case (StringCreateResult.StringCreateFailed error) (#panic))))
          (#let status #i64 (#println (#borrow owned)))
          (#call String::free ((string owned)))
          (#return ())\n  );\n}}\n"
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
    let source = "#fn third {
  #params = ();
  #returns = ();
  #body = (
    (#call print-trace ((text (#call-graph))))
    (#return ())
  );
}
#fn second {
  #params = ();
  #returns = ();
  #body = (
    (#call third ())
    (#return ())
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#call second ())
    (#call second ())
    (#return 42u64)\n  );\n}\n";
    assert_eq!(
        run(source),
        "main:21 -> second:13 -> third:5\nmain:22 -> second:13 -> third:5\n"
    );
}

#[test]
fn main_trace_and_live_distinct_trace_sites() {
    let source = "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let first (#slice #char) (#call-graph))
    (#let second (#slice #char) (#call-graph))
    (#call print-trace ((text first)))
    (#call print-trace ((text second)))
    (#return 42u64)\n  );\n}\n";
    assert_eq!(run(source), "main:5\nmain:6\n");
}

#[test]
fn only_the_executed_branch_appears() {
    let source = "#fn leaf {
  #params = ();
  #returns = ();
  #body = (
    (#call print-trace ((text (#call-graph))))
    (#return ())
  );
}
#fn left {
  #params = ();
  #returns = ();
  #body = (
    (#call leaf ())
    (#return ())
  );
}
#fn right {
  #params = ();
  #returns = ();
  #body = (
    (#call leaf ())
    (#return ())
  );
}
#fn choose {
  #params = ((condition #bool));
  #returns = ();
  #body = (
    (#if condition (#call left ()) (#call right ()))
    (#return ())
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#call choose ((condition true)))
    (#call choose ((condition false)))
    (#return 42u64)\n  );\n}\n";
    assert_eq!(
        run(source),
        "main:37 -> choose:29 -> left:13 -> leaf:5\nmain:38 -> choose:29 -> right:21 -> leaf:5\n"
    );
}

#[test]
fn implicit_clone_hooks_participate_in_the_chain() {
    let source = "#struct Value () ((number #u64))
#fn Value::clone {
  #params = ((value Value));
  #returns = Value;
  #body = (
    (#call print-trace ((text (#call-graph))))
    (#return value)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let value Value (#struct-literal Value ((number 42u64))))
    (#let copied Value (#clone value))
    (#return (#get copied number))\n  );\n}\n";
    assert_eq!(run(source), "main:15 -> Value::clone:6\n");
}

#[test]
fn thread_workers_receive_owned_caller_contexts() {
    let source = "#fn worker {
  #params = ();
  #returns = #u64;
  #body = (
    (#call print-trace ((text (#call-graph))))
    (#return 42u64)
  );
}
#generate #thread-spawn ((task Task) (worker worker))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let-else (Task::SpawnResult.Ok running) Task::SpawnResult
      (#call Task::spawn ())
      (#panic))
    (#return (#match (#call Task::join ((task running)))
      (#case (Task::JoinResult.Ok answer) answer)
      (#case (Task::JoinResult.Error (#tuple retry error)) (#panic))))\n  );\n}\n";
    assert_eq!(run(source), "main:15 -> worker:5\n");
}

#[test]
fn async_validation_witnesses_keep_their_original_checks() {
    let source = "#fn report {
  #params = ();
  #returns = ();
  #body = (
    (#call print-trace ((text (#call-graph))))
    (#return ())
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
    (function (#fn work () #u64
      (#call report ())
      (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let waker #u64 0u64)
    (#return (#match (#call Work::poll ((task (#call work ())) (waker (#borrow waker))))
      (#case (Work::Poll.Ready value) value)
      (#case (Work::Poll.Pending pending) (#block (#forget pending) (#unreachable)))))\n  );\n}\n";
    let output = run(source);
    assert!(output.starts_with("main:18 -> Work::poll:"), "{output}");
    assert!(output.ends_with(" -> report:5\n"), "{output}");
}

#[test]
fn trace_views_cannot_escape_their_stack_storage() {
    let program = lim::parse_program(
        "#fn trace {
  #params = ();
  #returns = (#slice #char);
  #body = ( (#return (#call-graph))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}\n",
    )
    .unwrap();
    assert!(lim::check_types(&program).is_err());
}

#[test]
fn trace_requires_no_arguments() {
    assert!(lim::parse_program("#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#call-graph 1u64) (#return 42u64)\n  );\n}\n").is_err());
}

#[test]
fn shared_callees_do_not_expand_into_every_possible_path() {
    let mut source = "#fn step0 {\n  #params = ();\n  #returns = #usize;\n  #body = ( (#return (#slice-len (#call-graph)))\n  );\n}\n".to_owned();
    for index in 1..=24 {
        let child = index - 1;
        source.push_str(&format!(
            "#fn step{index} {{
  #params = ();
  #returns = #usize;
  #body = (
            (#return (#usize::add-wrap (#call step{child} ()) (#call step{child} ())))\n  );\n}}\n"
        ));
    }
    source.push_str("#fn main {\n  #params = ();\n  #returns = #usize;\n  #body = ( (#return (#call step24 ()))\n  );\n}\n");
    let program = lim::parse_program(&source).unwrap();
    // More than sixteen million call paths still need only one append helper.
    assert_eq!(program.items.len(), 27);
}
