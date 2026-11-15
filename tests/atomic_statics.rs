mod support;

use std::{process::Command, time::Duration};

const SOURCE: &str = r#"
#type Counter (#atomic #u32)
#struct Nested () ((padding #u64) (counters (#array Counter 2)))
#enum State () ((State.Empty) (State.Active (#atomic #u16)))
#static total (#atomic #u64) (#atomic-init #u64 0u64)
#static counts Nested (#struct-literal Nested ((padding 99u64)
    (counters (#array-of (#array Counter 2) (#atomic-init #u32 3u32) (#atomic-init #u32 5u32)))))
#static current State (State.Active (#atomic-init #u16 7u16))
#static small (#atomic #i8) (#atomic-init #i8 -1i8)
#static readOnly #u64 17u64
#fn main () #u64
    (#unsafe (#atomic-store (#borrow total) 42u64 #memory-relaxed))
    (#let old #u32 (#unsafe (#atomic-fetch-add
      (#borrow (#index (#get counts counters) 1usize)) 1u32 #memory-relaxed)))
    (#assert (#u32::eq old 5u32))
    (#assert (#u32::eq (#unsafe (#atomic-load (#borrow (#index (#get counts counters) 1usize)) #memory-relaxed)) 6u32))
    (#assert (#u64::eq (#unsafe (#get counts padding)) 99u64))
    (#let state (#ref State) (#unsafe (#borrow current)))
    (#let active (#ref (#atomic #u16)) (#borrow (#get-payload state State.Active 0)))
    (#atomic-store active 8u16 #memory-relaxed)
    (#assert (#u16::eq (#atomic-load active #memory-relaxed) 8u16))
    (#assert (#i8::eq (#unsafe (#atomic-load (#borrow small) #memory-relaxed)) -1i8))
    (#assert (#u64::eq (#unsafe readOnly) 17u64))
    (#return (#unsafe (#atomic-load (#borrow total) #memory-relaxed)))
"#;

#[test]
fn constant_atomic_statics_and_nested_fields_use_writable_native_storage() {
    let scratch = support::Scratch::new("atomic-statics");
    let assembly = lim::compile_source_to_assembly(
        SOURCE,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    for name in ["total", "counts", "current", "small", "readOnly"] {
        let prefix = &assembly[..assembly.find(&format!("{name}:\n")).unwrap()];
        let data = prefix.rfind("\n.data\n");
        let rodata = prefix.rfind(".section .rodata\n");
        if name == "readOnly" {
            assert!(rodata > data, "immutable static must remain read-only");
        } else {
            assert!(data > rodata, "{name} must have writable atomic storage");
        }
    }
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
    assert_eq!(status.code(), Some(42), "{status:?}: {stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn atomic_static_initializer_still_rejects_runtime_calls() {
    let source = "#fn calculate () #u64 (#return 1u64)
#static total (#atomic #u64) (#atomic-init #u64 (#call calculate ()))
#fn main () #u64 (#return 42u64)\n";
    let scratch = support::Scratch::new("atomic-static-nonconstant");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("static initialization must be constant");
    assert_eq!(error.code, lim::DiagnosticCode::Codegen, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "(#call calculate ())");
}
