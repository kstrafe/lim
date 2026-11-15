mod support;

use std::{process::Command, time::Duration};

fn compile(source: &str, target: lim::TargetDescription) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("ref-ptr-check");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
}

fn run(source: &str, target: lim::TargetDescription) {
    let assembly = compile(source, target).unwrap_or_else(|e| panic!("{e:?}\n{source}"));
    let scratch = support::Scratch::new("ref-ptr-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let mut command = if target == lim::TargetDescription::AARCH64_LINUX {
        let mut command = Command::new("qemu-aarch64");
        command.arg(&binary);
        command
    } else {
        Command::new(&binary)
    };
    let (status, out, err) = support::run(&mut command, Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{err:?}\n{source}");
    assert!(out.is_empty() && err.is_empty());
}

#[test]
fn scalar_and_aggregate_roundtrips_lend_all_four_reference_kinds() {
    for target in [
        lim::TargetDescription::X86_64_SYSTEM_V,
        lim::TargetDescription::AARCH64_LINUX,
    ] {
        for pinned in [false, true] {
            for mutable in [false, true] {
                for (ty, init, read) in [
                    ("#u64", "42u64", "(#deref restored)"),
                    ("#u8", "42u8", "(#as (#deref restored) #u64)"),
                    (
                        "Pair",
                        "(#struct-literal Pair ((left 40u64) (right 2u64)))",
                        "(#u64::add-wrap (#get restored left) (#get restored right))",
                    ),
                ] {
                    let pin = if pinned { "pin-" } else { "" };
                    let suffix = if mutable { "-mut" } else { "" };
                    let source = format!(
                        r#"
#struct Pair () ((left #u64) (right #u64))
#fn extract {{
  #params = ((view (#{pin}ref{suffix} {ty})));
  #returns = (#ptr{suffix} {ty});
  #body = (
                          (#return (#ref-ptr view))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                          (#let-mut owner {ty} {init})
                          (#let view (#{pin}ref{suffix} {ty}) (#{suffix}0borrow{suffix}1 owner))
                          (#let pointer (#ptr{suffix}2 {suffix}3) (#ref-ptr view))
                          (#assert (#usize::eq (#ptr-address pointer) (#ptr-address (#ref-ptr view))))
                          (#assert (#usize::eq (#ptr-address pointer) (#ptr-address (#call extract ((view view))))))
                          (#let restored (#{suffix}4ref{suffix}5 {suffix}6)
                            (#unsafe (#{suffix}7ptr-borrow{suffix}8 view pointer)))
                          (#drop view)
                          (#let answer #u64 {suffix}9)
                          (#drop restored)
                          (#forget owner) (#return answer)
  );
}}
"#
                    );
                    run(&source, target);
                }
            }
        }
    }
}

#[test]
fn extraction_does_not_retain_a_loan_and_reference_remains_writable() {
    run(
        r#"#fn escape {
  #params = ();
  #returns = (#ptr-mut #u64);
  #body = (
          (#let-mut owner #u64 1u64)
          (#let view (#ref-mut #u64) (#borrow-mut owner))
          (#let pointer (#ptr-mut #u64) (#ref-ptr view))
          (#deref-set view 42u64)
          (#drop view) (#set owner 0u64) (#return pointer)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let pointer (#ptr-mut #u64) (#call escape ()))
          (#assert (#bool::not (#ptr-is-null pointer)))
          (#let-mut value #u64 1u64)
          (#let expected (#ptr-mut #u64) (#unsafe (#addr-of-mut value)))
          (#let view (#ref-mut #u64) (#borrow-mut value))
          (#let address (#ptr-mut #u64) (#ref-ptr view))
          (#assert (#usize::eq (#ptr-address address) (#ptr-address expected)))
          (#assert (#u64::eq (#unsafe (#ptr-read address)) 1u64))
          (#deref-set view 42u64)
          (#return (#deref view))
  );
}
"#,
        lim::TargetDescription::X86_64_SYSTEM_V,
    );
}

#[test]
fn projected_exclusive_handles_are_lent_without_being_moved() {
    for pin in ["", "pin-"] {
        let source = format!(
            r#"
#struct Holder () ((view (#{pin}ref-mut #u64)))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let-mut value #u64 42u64)
              (#let holder Holder (#struct-literal Holder ((view (#{pin}borrow-mut value)))))
              (#let first (#ptr-mut #u64) (#ref-ptr (#get holder view)))
              (#let second (#ptr-mut #u64) (#ref-ptr (#get holder view)))
              (#assert (#usize::eq (#ptr-address first) (#ptr-address second)))
              (#let answer #u64 (#deref (#get holder view)))
              (#forget holder) (#return answer)
  );
}}
"#
        );
        run(&source, lim::TargetDescription::X86_64_SYSTEM_V);
    }
}

#[test]
fn nonreferences_and_fat_slices_are_rejected() {
    for operand in [
        "42u64",
        "(#ptr-null (#ptr #u64))",
        "(#borrow-slice values)",
        "(#borrow-slice-mut values)",
    ] {
        let source = format!("#fn main {{\n  #params = ();\n  #returns = ();\n  #body = ( (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 42u64)) (#let pointer (#ptr #u64) (#ref-ptr {operand})) (#forget values) (#return ())\n  );\n}}\n");
        let error = compile(&source, lim::TargetDescription::X86_64_SYSTEM_V).unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
        assert!(
            error
                .message
                .contains("ref-ptr requires an ordinary or pinned reference"),
            "{error:?}"
        );
    }
}

#[test]
fn extraction_is_safe_but_raw_access_and_reborrowing_are_unsafe() {
    for operation in [
        "(#ptr-read pointer)",
        "(#ptr-write pointer 42u64)",
        "(#ptr-borrow view pointer)",
    ] {
        let source = format!("#fn main {{\n  #params = ();\n  #returns = ();\n  #body = ( (#let-mut owner #u64 42u64) (#let view (#ref-mut #u64) (#borrow-mut owner)) (#let pointer (#ptr-mut #u64) (#ref-ptr view)) {operation} (#drop view) (#return ())\n  );\n}}\n");
        let error = compile(&source, lim::TargetDescription::X86_64_SYSTEM_V).unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Unsafe, "{error:?}");
        assert!(error.message.contains("unsafe"), "{error:?}");
    }
}

#[test]
fn raw_pointers_do_not_derive_thread_properties() {
    let program = lim::parse_program(
        "#struct Shared () ((pointer (#ptr #u64)))\n#struct Exclusive () ((pointer (#ptr-mut #u64)))\n",
    )
    .unwrap();
    for ty in [
        lim::Type::Named("Shared".into()),
        lim::Type::Named("Exclusive".into()),
        lim::Type::RawPointer {
            mutable: false,
            target: Box::new(lim::Type::U64),
        },
        lim::Type::RawPointer {
            mutable: true,
            target: Box::new(lim::Type::U64),
        },
    ] {
        for property in [lim::ThreadProperty::Send, lim::ThreadProperty::Sync] {
            assert!(!lim::type_has_thread_property(&program, &ty, property).unwrap());
        }
    }
}
