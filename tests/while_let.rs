//! A while-let scrutinee is evaluated once per iteration, including its exit.
mod support;

use std::{process::Command, time::Duration};

fn run(source: &str) {
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let scratch = support::Scratch::new("while-let");
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
fn scrutinee_effects_and_payload_are_not_repeated() {
    run("(#enum Choice () ((Choice.Chosen #u64) Choice.Empty))
      (#fn take ((counter (#ref-mut #u64))) Choice
        (#let before #u64 (#deref counter))
        (#deref-set counter (#u64::add-wrap before 1u64))
        (#return (#if (#u64::eq before 0u64) (Choice.Chosen 40u64) Choice.Empty)))
      (#fn main () #u64
        (#let-mut count #u64 0u64) (#let-mut total #u64 0u64)
        (#while-let (Choice.Chosen value) (#call take ((counter (#borrow-mut count))))
          (#assert (#u64::eq value 40u64)) (#set total value))
        (#assert (#u64::eq count 2u64))
        (#return (#u64::add-wrap total count)))");
}

#[test]
fn loop_control_targets_the_single_evaluation_loop() {
    for control in ["(#continue)", "(#break)", "(#break-to iteration)"] {
        run(&format!(
            "(#enum Choice () ((Choice.Chosen #u64) Choice.Empty))
          (#fn main () #u64
            (#let-mut choice Choice (Choice.Chosen 42u64))
            (#let-mut result #u64 0u64)
            (#label iteration (#while-let (Choice.Chosen value) choice
              (#set result value) (#set choice Choice.Empty) {control}))
            (#return result))"
        ));
    }
}

#[test]
fn single_evaluation_does_not_release_payload_borrows_early() {
    let source = "(#enum Choice () ((Choice.Chosen (#ref #u64)) Choice.Empty))
      (#fn main () #u64
        (#let-mut owner #u64 42u64)
        (#let-mut choice Choice (Choice.Chosen (#borrow owner)))
        (#while-let (Choice.Chosen view) choice
          (#set owner 0u64) (#assert (#u64::eq (#deref view) 42u64))
          (#set choice Choice.Empty)) (#return owner))";
    let program = lim::parse_program(source).unwrap();
    assert!(lim::check_types(&program).is_err());
}
