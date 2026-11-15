mod support;

use std::{fs, process::Command, time::Duration};

const TRACE: &str = "
#fn mark {
  #params = ((byte #u8) (value #u64));
  #returns = #u64;
  #effects = (#global-access #io); #body = (
      (#let written #i64 (#unsafe (#linux-syscall #i64 1usize (1i64 (#borrow byte) 1usize))))
      (#assert (#i64::eq written 1i64)) (#return value)\n  );\n}\n";

fn trace(source: &str, expected: &[u8], success: bool) {
    for target in [
        lim::TargetDescription::X86_64_SYSTEM_V,
        lim::TargetDescription::AARCH64_LINUX,
    ] {
        for audits in [false, true] {
            let scratch = support::Scratch::new("written-order");
            let path = scratch.path().join("main.lim");
            let cache = scratch.path().join("cache");
            let mut config = lim::CompileConfig::default();
            if audits {
                config.set("contracts", "check");
            }
            let mut previous = None;
            for _ in 0..2 {
                let source = if target == lim::TargetDescription::AARCH64_LINUX {
                    source.replace("#i64 1usize", "#i64 64usize")
                } else {
                    source.to_owned()
                };
                let assembly =
                    lim::compile_source_to_assembly(&source, &path, &config, &cache, target)
                        .unwrap_or_else(|error| panic!("{}\n{source}", error.message));
                if let Some(previous) = &previous {
                    assert_eq!(previous, &assembly, "warm cache changed execution");
                }
                previous = Some(assembly.clone());
                let binary = scratch.path().join("program");
                lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
                let mut command = if target == lim::TargetDescription::AARCH64_LINUX {
                    let mut command = Command::new("qemu-aarch64");
                    command.arg(&binary);
                    command
                } else {
                    Command::new(binary)
                };
                command.current_dir(scratch.path());
                let (status, stdout, stderr) =
                    support::run(&mut command, Duration::from_secs(5), 8192).unwrap();
                assert_eq!(
                    stdout,
                    expected,
                    "{status:?}: {}",
                    String::from_utf8_lossy(&stderr)
                );
                if success {
                    assert_eq!(
                        status.code(),
                        Some(42),
                        "{}",
                        String::from_utf8_lossy(&stderr)
                    );
                } else {
                    assert!(!status.success());
                }
            }
        }
    }
}

#[test]
fn labels_route_values_without_reordering_effects_even_if_signature_changes() {
    for parameters in ["(left #u64) (right #u64)", "(right #u64) (left #u64)"] {
        let source = format!(
            "{TRACE}
#fn subtract {{
  #params = ({parameters});
  #returns = #u64;
  #effects = ((#effects-of mark)); #body = (
              (#call mark ((byte 67u8) (value 0u64)))
              (#return (#u64::sub-wrap left right))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of mark) (#effects-of subtract)); #body = ( (#return (#call subtract
              ((right (#call mark ((byte 65u8) (value 2u64))))
               (left (#call mark ((byte 66u8) (value 44u64)))))))\n  );\n}}\n"
        );
        trace(&source, b"ABC", true);
        trace(&source.replace("#call ", ""), b"ABC", true);
    }
}

#[test]
fn struct_layout_and_projection_keep_written_initialization_effects() {
    trace(
        &format!(
            "{TRACE}
#struct Pair () ((left #u64) (right #u64))
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of mark)); #body = (
          (#let pair Pair (#struct-literal Pair
            ((right (#call mark ((byte 65u8) (value 2u64))))
             (left (#call mark ((byte 66u8) (value 44u64)))))))
          (#assert (#u64::eq (#get pair right) 2u64))
          (#let projected #u64 (#get (#struct-literal Pair
            ((right (#call mark ((byte 67u8) (value 0u64))))
             (left (#call mark ((byte 68u8) (value 0u64)))))) left))
          (#return (#u64::sub-wrap (#get pair left) (#get pair right)))\n  );\n}}\n"
        ),
        b"ABCD",
        true,
    );
}

#[test]
fn strict_intrinsic_roles_survive_reversed_evaluation() {
    trace(
        &format!(
            "{TRACE}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of mark)); #body = (
        (#return (#call #u64::sub-wrap
          ((right (#call mark ((byte 65u8) (value 2u64))))
           (left (#call mark ((byte 66u8) (value 44u64)))))))
  );\n}}\n"
        ),
        b"AB",
        true,
    );
}

#[test]
fn a_nonreturning_argument_stops_later_values_and_callee_entry() {
    trace(
        &format!(
            "{TRACE}
#fn fail {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of mark)); #body = ( (#call mark ((byte 65u8) (value 0u64))) (#return (#panic))
  );
}}
#fn callee {{
  #params = ((left #u64) (right #u64));
  #returns = #u64;
  #effects = ((#effects-of mark)); #body = (
          (#return (#call mark ((byte 67u8) (value 42u64))))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of callee) (#effects-of fail) (#effects-of mark)); #body = ( (#return (#call callee
          ((right (#call fail ()))
           (left (#call mark ((byte 66u8) (value 0u64)))))))\n  );\n}}\n"
        ),
        b"A",
        false,
    );
}

#[test]
fn later_writes_respect_earlier_argument_loans_and_report_authored_spans() {
    let prefix =
        "#fn change {
  #params = ((target (#ref-mut #u64)));
  #returns = #u64;
  #body = ( (#deref-set target 42u64) (#return 0u64)
  );
}
#fn read {
  #params = ((view (#ref #u64)) (ignored #u64));
  #returns = #u64;
  #body = ( (#return (#deref view))\n  );\n}\n";
    let write = "(ignored (#call change ((target (#borrow-mut owner)))))";
    let borrow = "(view (#borrow owner))";
    let valid = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut owner #u64 0u64)
        (#return (#call read ({write} {borrow})))
  );\n}}\n"
    );
    lim::check_types(&lim::parse_program(&valid).unwrap()).unwrap();
    let invalid = valid.replace(&format!("{write} {borrow}"), &format!("{borrow} {write}"));
    let scratch = support::Scratch::new("written-order-loan");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("borrow"), "{}", error.message);
    let span = error.span.expect("authored conflicting argument span");
    assert_eq!(&invalid[span.start..span.end], "#borrow-mut");
    assert!(
        error
            .labels
            .iter()
            .any(|label| invalid[label.span.start..label.span.end].contains("#borrow")),
        "missing original loan label: {error:?}"
    );
}

#[test]
fn aliases_and_direct_file_calls_keep_written_order() {
    let scratch = support::Scratch::new("written-order-files");
    fs::write(
        scratch.path().join("helper.lim"),
        format!(
            "{TRACE}
#fn subtract {{
  #params = ((left #u64) (right #u64));
  #returns = #u64;
  #body = ( (#return (#u64::sub-wrap left right))\n  );\n}}\n"
        ),
    )
    .unwrap();
    let path = scratch.path().join("main.lim");
    let source = "#alias mark = ./helper.lim::mark
#alias subtract = ./helper.lim::subtract
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of mark));
  #body = ( (#return (subtract {
          right = mark { byte = 65u8; value = 2; };
          left = mark { byte = 66u8; value = 44; };
        }))\n  );\n}\n";
    for source in [
        source.to_owned(),
        source.replace("(subtract {", "(./helper.lim::subtract {"),
    ] {
        let assembly = lim::compile_source_to_assembly(
            &source,
            &path,
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let binary = scratch.path().join("program");
        lim::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let (status, stdout, _) =
            support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
        assert_eq!(status.code(), Some(42));
        assert_eq!(stdout, b"AB");
    }
}

#[test]
fn contract_requirements_use_the_state_after_every_argument() {
    let source = "#fn positive {
  #params = ((value #u64));
  #returns = #bool;
  #body = ( (#return (#u64::gt value 0u64))
  );
}
#fn accept {
  #params = ((value #u64) (ignored ()));
  #returns = #u64;
  #body = (
          (#requires (#call positive ((value value)))) (#return value)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut number #u64 42u64)
          (#return (#if-valid (#call positive ((value number)))
            (#call accept ((ignored (#block (#set number 0u64) ())) (value number)))
            0u64))\n  );\n}\n";
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("evidence") || error.contains("require"),
        "{error}"
    );
}
