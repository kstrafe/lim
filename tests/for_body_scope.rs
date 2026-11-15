//! For-body declarations remain live through the step, not the next condition.
mod support;

use std::{process::Command, time::Duration};

const CONTEXT: &str = "#struct Resource (#linear) ((value #u64))\n ";

fn run(body: &str) {
    let program = lim::parse_program(&format!("{CONTEXT} {body}")).unwrap();
    lim::check_types(&program).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let scratch = support::Scratch::new("for-body-scope");
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn step_consumes_the_body_owner_before_iteration_scope_ends() {
    for control in ["", "(#continue)", "(#continue-to iteration)"] {
        run(&format!(
            "#fn main () #u64
            (#let-mut index #u64 0u64) (#let-mut result #u64 0u64)
            (#label iteration (#for () (#u64::lt index 1u64)
              (#block (#set result (#get token value)) (#forget token) (#set index 1u64))
              (#let token Resource (#struct-literal Resource ((value 42u64)))) {control}))
            (#return result)\n"
        ));
    }
}

#[test]
fn break_consumes_body_owner_without_running_step() {
    run("#fn main () #u64
        (#let-mut result #u64 0u64)
        (#for () true (#assert false)
          (#let token Resource (#struct-literal Resource ((value 42u64))))
          (#set result (#get token value)) (#forget token) (#break))
        (#return result)\n");
}

#[test]
fn body_scope_still_requires_explicit_linear_consumption() {
    for tail in ["(#break)", "(#continue)", ""] {
        let source = format!(
            "{CONTEXT}
#fn main () #u64
            (#let-mut index #u64 0u64)
            (#for () (#u64::lt index 1u64) (#set index 1u64)
              (#let token Resource (#struct-literal Resource ((value 42u64)))) {tail})
            (#return 42u64)
"
        );
        let program = lim::parse_program(&source).unwrap();
        assert!(lim::check_types(&program).is_err(), "{tail}");
    }
}

#[test]
fn a_step_cannot_return_a_reference_to_a_body_local() {
    let source = "#fn escape () (#ref #u64)
        (#for () true (#return (#borrow owner))
          (#let owner #u64 42u64)) (#return (#unreachable))\n";
    let program = lim::parse_program(source).unwrap();
    assert!(lim::check_types(&program).is_err());
}

#[test]
fn a_step_can_return_an_external_reference_without_losing_its_origin() {
    run("#fn select ((source (#ref #u64))) (#ref #u64)
        (#for () true (#return source) (#let body-ran #bool true))
        (#return source)
#fn main () #u64
          (#let owner #u64 42u64)
          (#let view (#ref #u64) (#call select ((source (#borrow owner)))))
          (#return (#deref view))\n");
}

#[test]
fn continue_before_initialization_cannot_supply_the_step_owner() {
    let source = format!(
        "{CONTEXT}
#fn main () #u64
        (#for () true (#forget token)
          (#continue) (#let token Resource (#struct-literal Resource ((value 42u64)))))
        (#return 42u64)
"
    );
    let program = lim::parse_program(&source).unwrap();
    assert!(lim::check_types(&program).is_err());
}

#[test]
fn a_step_cannot_store_a_body_borrow_past_the_iteration() {
    let source = "#fn main () #u64
        (#let outside #u64 0u64)
        (#let-mut escaped (#ref #u64) (#borrow outside))
        (#for (#let-mut index #u64 0u64) (#u64::lt index 1u64)
          (#block (#set escaped (#borrow owner)) (#set index 1u64))
          (#let owner #u64 42u64))
        (#return (#deref escaped))\n";
    let program = lim::parse_program(source).unwrap();
    assert!(lim::check_types(&program).is_err());
}

#[test]
fn nested_break_and_continue_cleanup_only_the_exited_body_scopes() {
    for transfer in ["(#continue-to outer)", "(#break-to outer)"] {
        run(&format!(
            "#fn main () #u64
            (#let-mut result #u64 0u64) (#let-mut count #u64 0u64)
            (#label outer (#for () (#u64::lt count 1u64)
              (#block (#set result (#get outer-token value)) (#forget outer-token) (#set count 1u64))
              (#let outer-token Resource (#struct-literal Resource ((value 42u64))))
              (#for () true ()
                (#let inner-token Resource (#struct-literal Resource ((value 1u64))))
                (#forget inner-token)
                {cleanup} {transfer})))
            (#return result)\n",
            cleanup = if transfer.contains("break") {
                "(#set result (#get outer-token value)) (#forget outer-token)"
            } else {
                ""
            }
        ));
    }
}
