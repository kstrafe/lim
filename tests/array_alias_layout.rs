mod support;

use std::{process::Command, time::Duration};

fn source(length: usize, global: bool) -> String {
    let values = (0..length)
        .map(|index| if index == 0 { "17u64" } else { "25u64" })
        .collect::<Vec<_>>()
        .join(" ");
    let row = format!("(#array-of Row {values})");
    let grid = format!("(#array-of Grid {row} (#array-repeat 25u64))");
    let declaration = if global {
        format!("(#static table Grid {grid})")
    } else {
        String::new()
    };
    let extra = if global {
        "(#assert (#u64::eq (#call inspect (: values (#unsafe table))) 42u64))"
    } else {
        ""
    };
    format!(
        "(#type Scalar #u64) (#type Row (#array Scalar {length}))
      (#type RowAlias Row) (#type Grid (#array RowAlias 2)) {declaration}
      (#fn make-row () RowAlias (#return {row}))
      (#fn make-grid () Grid (#return {grid}))
      (#fn inspect (: values Grid) #u64
        (#return (#u64::add-wrap (#index (#index values 0usize) 0usize)
          (#index (#index values 1usize) {last}usize))))
      (#fn main () #u64
        (#let local Grid {grid})
        (#assert (#u64::eq (#call inspect (: values local)) 42u64))
        (#let returned Grid (#call make-grid ()))
        (#assert (#u64::eq (#call inspect (: values returned)) 42u64))
        (#let returned-row RowAlias (#call make-row ()))
        (#assert (#u64::eq (#index returned-row 0usize) 17u64)) {extra}
        (#return (#call inspect (: values {grid}))))",
        last = length - 1
    )
}

fn run(source: &str) {
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let scratch = support::Scratch::new("array-alias-layout");
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
    assert_eq!(status.code(), Some(42), "{status:?} {stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn aliased_array_constructors_keep_register_and_indirect_layouts() {
    for length in [2, 8] {
        run(&source(length, false));
    }
}

#[test]
fn aliased_static_array_constructors_keep_nested_layouts() {
    for length in [2, 8] {
        run(&source(length, true));
    }
}

#[test]
fn an_alias_annotation_does_not_bypass_constructor_length_checking() {
    let source = "(#type Row (#array #u64 2))
      (#fn main () #u64 (#let row Row (#array-of Row 42u64)) (#return 42u64))";
    let error = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("expects 2 elements"), "{error}");
}
