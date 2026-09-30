fn assembly(source: &str) -> Result<String, String> {
    let program = lim::parse_program(source)?;
    lim::generate_assembly_for_target(&program, lim::TargetDescription::X86_64_SYSTEM_V)
}

#[test]
fn global_reference_origins_remain_in_scope_across_branches() {
    assembly(
        r#"
      (#let VALUE u64 42u64)
      (#fn select ((condition bool)) (#ref u64)
        (#let result (#ref u64)
          (#if condition
            (#block (#borrow VALUE))
            (#block (#borrow VALUE))))
        (#return result))
      (#fn main () u64
        (#return (#deref (#call select (: condition true)))))
    "#,
    )
    .unwrap();
}

#[test]
fn sharing_globals_does_not_allow_shadowing() {
    for body in [
        "(#fn bad ((VALUE u64)) u64 (#return VALUE))",
        "(#fn bad () u64 (#let VALUE u64 1u64) (#return VALUE))",
        "(#fn bad () u64 (#return (#block (#let VALUE u64 1u64) VALUE)))",
    ] {
        let error = lim::parse_program(&format!("(#let VALUE u64 42u64) {body}")).unwrap_err();
        assert!(error.contains("shadowing is not allowed"), "{error}");
    }
}

#[test]
fn local_reference_escapes_still_fail_with_many_globals() {
    let mut source = String::new();
    for i in 0..512 {
        source.push_str(&format!("(#let GLOBAL{i} u64 {i}u64)\n"));
    }
    source.push_str("(#fn bad () (#ref u64) (#let value u64 42u64) (#return (#borrow value)))");
    assert!(assembly(&source).unwrap_err().contains("local"));
}
