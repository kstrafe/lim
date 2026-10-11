mod support;

use std::{process::Command, time::Duration};

#[test]
fn large_argument_diverging_match_and_if_arms_emit_traps() {
    use std::os::unix::process::ExitStatusExt;

    let source = r#"
      (#enum Choice (First Second))
      (#fn read (: values (#array #u64 10)) #u64
        (#let result #u64 (#index values 9usize))
        (#forget values) (#return result))
      (#fn main () #u64
        (#let choice Choice First)
        (#let first #u64 (#call read (: values
          (#match choice
            (#case First (#array-repeat 42u64))
            (#case Second (#unreachable))))))
        (#let second #u64 (#call read (: values
          (#if #true (#array-repeat 1u64) (#unreachable)))))
        (#return (#u64.+.wrap first second)))
    "#;
    for (source, expected) in [
        (source.to_owned(), Some(43)),
        (
            source.replace("choice Choice First", "choice Choice Second"),
            None,
        ),
        (source.replace("#if #true", "#if #false"), None),
    ] {
        let scratch = support::Scratch::new("large-argument-divergence");
        let assembly = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, &source, "main.lim")));
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
        assert_eq!(status.code(), expected, "{stderr:?}");
        if expected.is_none() {
            assert_eq!(status.signal(), Some(4), "{status:?}");
        }
        assert!(stdout.is_empty() && stderr.is_empty());
    }
}

#[test]
fn large_enum_reference_reads_writes_and_matches_use_storage() {
    for pinned in [false, true] {
        let (reference, borrow, read, write) = if pinned {
            ("#pin-ref-mut", "#pin-borrow-mut", "#pin-read", "#pin-write")
        } else {
            ("#ref-mut", "#borrow-mut", "#deref", "#deref-set")
        };
        let source = format!(
            "(#struct Large (: values (#array #u64 10)))
          (#enum Container ((Empty) (Full Large))) (#linear Container)
          (#struct Wrapper (: item Container)) (#linear Wrapper)
          (#fn extract (: slot ({reference} Container)) Large
            (#let previous Container (#unsafe ({read} slot)))
            (#unsafe ({write} slot Empty))
            (#return (#match previous (#case Empty (#unreachable)) (#case (Full value) value))))
          (#fn main () #u64
            (#let-mut owner Container (Full (#struct-literal Large
              (: values (#array-repeat 42u64)))))
            (#let result Large (#call extract (: slot ({borrow} owner))))
            (#assert (#u64.== (#index (#get result values) 9usize) 42u64))
            (#forget result)
            (#let view ({reference} Container) ({borrow} owner))
            (#unsafe (#forget ({read} view)))
            (#unsafe ({write} view Empty))
            (#drop view)
            (#forget owner)
            (#let wrapped Wrapper (#struct-literal Wrapper (: item (Full
              (#struct-literal Large (: values (#array-repeat 42u64)))))))
            (#let answer #u64 (#match (#get wrapped item)
              (#case Empty (#unreachable))
              (#case (Full payload) (#block
                (#let value #u64 (#index (#get payload values) 0usize))
                (#forget payload) value))))
            (#forget wrapped) (#return answer))"
        );
        let scratch = support::Scratch::new("large-reference-values");
        let assembly = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, &source, "main.lim")));
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
}
