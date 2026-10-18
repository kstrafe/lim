fn assembly(source: &str) -> Result<String, String> {
    let program = lim::parse_program(source)?;
    lim::generate_assembly_for_target(&program, lim::TargetDescription::X86_64_SYSTEM_V)
}

#[test]
fn global_reference_origins_remain_in_scope_across_branches() {
    assembly(
        r#"
      (#let vALUE #u64 42u64)
      (#fn select ((condition #bool)) (#ref #u64)
        (#let result (#ref #u64)
          (#if condition
            (#block (#borrow vALUE))
            (#block (#borrow vALUE))))
        (#return result))
      (#fn main () #u64
        (#return (#deref (#call select (: condition true)))))
    "#,
    )
    .unwrap();
}

#[test]
fn sharing_globals_does_not_allow_shadowing() {
    for body in [
        "(#fn bad ((vALUE #u64)) #u64 (#return vALUE))",
        "(#fn bad () #u64 (#let vALUE #u64 1u64) (#return vALUE))",
        "(#fn bad () #u64 (#return (#block (#let vALUE #u64 1u64) vALUE)))",
    ] {
        let error = lim::parse_program(&format!("(#let vALUE #u64 42u64) {body}")).unwrap_err();
        assert!(error.contains("shadowing is not allowed"), "{error}");
    }
}

#[test]
fn local_reference_escapes_still_fail_with_many_globals() {
    let mut source = String::new();
    for i in 0..512 {
        source.push_str(&format!("(#let GLOBAL{i} #u64 {i}u64)\n"));
    }
    source.push_str("(#fn bad () (#ref #u64) (#let value #u64 42u64) (#return (#borrow value)))");
    assert!(assembly(&source).unwrap_err().contains("local"));
}

#[test]
fn global_types_are_visible_in_initializers_and_pattern_branches() {
    assembly(
        r#"
      (#let bASE #u64 40u64)
      (#let aNSWER #u64 (#u64::add-wrap bASE 2u64))
      (#enum Value () ((Value.Number #u64) (Value.Absent)))
      (#fn pick ((value Value)) #u64
        (#return (#match value
          (#case (Value.Number number) (#u64::add-wrap number bASE))
          (#case Value.Absent aNSWER))))
      (#fn main () #u64 (#return (#call pick (: value (Value.Number 2u64)))))
    "#,
    )
    .unwrap();
    assert!(assembly("(#let vALUE #bool true) (#fn main () #u64 (#return vALUE))").is_err());
}
