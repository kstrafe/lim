mod support;

use std::{process::Command, time::Duration};

fn run_on_both_targets(source: &str) {
    run_on_targets(
        source,
        &[
            lim::TargetDescription::X86_64_SYSTEM_V,
            lim::TargetDescription::AARCH64_LINUX,
        ],
    );
}

fn run_on_targets(source: &str, targets: &[lim::TargetDescription]) {
    for &target in targets {
        let program = lim::parse_program(source).unwrap();
        lim::check_types(&program).unwrap();
        let assembly = lim::generate_assembly_for_target(&program, target).unwrap();
        let scratch = support::Scratch::new("anonymous-type-position");
        let binary = scratch.path().join("program");
        lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
        let mut command = if target == lim::TargetDescription::AARCH64_LINUX {
            let mut command = Command::new("qemu-aarch64");
            command.arg(&binary);
            command
        } else {
            Command::new(&binary)
        };
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(5), 4096).unwrap();
        assert_eq!(status.code(), Some(42), "{target:?}: {stderr:?}\n{source}");
        assert!(stdout.is_empty() && stderr.is_empty());
    }
}

#[test]
fn tuple_and_array_constructors_lower_their_explicit_record_types() {
    run_on_both_targets(
        r#"
#fn main {
  #params = {}; #returns = #u64;
  #body = (
    (#let pair (#tuple { value = #u64; } #u64)
      (#tuple (#tuple { value = #u64; } #u64)
        (#record-literal { value = #u64; } { value = 40u64; }) 2u64))
    (#let array (#array { value = #u64; } 1)
      (#array-of (#array { value = #u64; } 1)
        (#record-literal { value = #u64; } { value = 40u64; })))
    (#assert (#u64::eq (#get (#index array 0usize) value) 40u64))
    (#return (#u64::add-wrap (#get (#get pair 0) value) (#get pair 1)))
  );
}
"#,
    );
}

#[test]
fn pointer_constructors_keep_their_explicit_pointee_record() {
    // AArch64 does not yet implement #ptr-null; type lowering is target-neutral.
    run_on_targets(
        r#"
#fn main {
  #params = {}; #returns = #u64;
  #body = (
    (#let pointer (#ptr { value = #u64; }) (#ptr-null (#ptr { value = #u64; })))
    (#let mutable-pointer (#ptr-mut { value = #u64; })
      (#ptr-null (#ptr-mut { value = #u64; })))
    (#assert (#ptr-is-null pointer))
    (#return (#if (#ptr-is-null mutable-pointer) 42u64 0u64))
  );
}
"#,
        &[lim::TargetDescription::X86_64_SYSTEM_V],
    );
}

#[test]
fn contextual_tuple_values_are_not_reinterpreted_as_types() {
    run_on_both_targets(
        r#"
#struct Point () ((value #u64))
#fn main {
  #params = {}; #returns = #u64;
  #body = (
    (#let pair (#tuple Point #u64)
      (#tuple (#struct-literal Point ((value 40u64))) 2u64))
    (#assert (#u64::eq (#get (#get pair 0) value) 40u64))
    (#let nested (#tuple (#tuple { value = #u64; } #u64) #u64)
      (#tuple (#tuple (#record-literal { value = #u64; } { value = 40u64; }) 1u64) 1u64))
    (#let answer #u64 (#u64::add-wrap
      (#get (#get (#get nested 0) 0) value)
      (#u64::add-wrap (#get (#get nested 0) 1) (#get nested 1))))
    (#forget nested)
    (#return answer)
  );
}
"#,
    );
}

#[test]
fn ordinary_and_distributed_variants_keep_structural_payload_types() {
    for declaration in [
        "#enum Choice () ((Choice.Full { value = #u64; }) Choice.Empty)",
        "#distributed-enum Choice ()\n#enum-contribute Choice (Choice.Full { value = #u64; })\n#enum-contribute Choice (Choice.Empty)",
    ] {
        run_on_both_targets(&format!(r#"
{declaration}
#fn main {{
  #params = {{}}; #returns = #u64;
  #body = (
    (#let choice Choice (#enum-literal Choice.Full
      (#record-literal {{ value = #u64; }} {{ value = 42u64; }})))
    (#return (#match choice
      (#case (Choice.Full payload) (#get payload value))
      (#case Choice.Empty 0u64)))
  );
}}
"#));
    }
}

#[test]
fn generated_empty_records_are_unit_and_evaluate_the_call_once() {
    run_on_both_targets(
        r#"
#gn make-empty { function; }
  `((#fn ,function {
    #params = { counter = (#ref-mut #u64); };
    #returns = {};
    #body = ((#deref-set counter (#u64::add-wrap (#deref counter) 1u64))
      (#return (#record-literal {} {})));
  }))
#generate make-empty { function = empty; }
#fn main {
  #params = {}; #returns = #u64;
  #body = (
    (#let-mut counter #u64 41u64)
    (#let {} = (empty { counter = (#borrow-mut counter); }))
    (#return counter)
  );
}
"#,
    );
    let source =
        "#fn main { #params = {}; #returns = #u64; #body = ((#let {} = 42u64) (#return 42u64)); }";
    let error = lim::parse_program(source)
        .and_then(|program| lim::check_types(&program))
        .unwrap_err();
    assert!(error.contains("Unit"), "{error}");
}
