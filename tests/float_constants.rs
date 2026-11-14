mod support;
use std::{fs, process::Command, time::Duration};

#[test]
fn floating_globals_preserve_width_bits_and_runtime_semantics() {
    let scratch = support::Scratch::new("float-constants");
    let root = scratch.path();
    let source = "
      (#const rounded #f32 (#f32::sub (#f32::add 16777216.0f32 1.0f32) 16777216.0f32))
      (#const forward #f64 (#f64::add base 0.5f64))
      (#const base #f64 1.5f64)
      (#const negativeZero #f64 -0.0f64)
      (#const infinity #f64 (#f64::div 1.0f64 0.0f64))
      (#const nan #f64 (#f64::div 0.0f64 0.0f64))
      (#struct Floats () ((small #f32) (large #f64)))
      (#static pair Floats (#struct-literal Floats ((large forward) (small rounded))))
      (#static values (#array #f64 2) (#array-of (#array #f64 2) negativeZero infinity))
      (#fn main () #u64
        (#let runtimeRounded #f32 (#f32::sub (#f32::add 16777216.0f32 1.0f32) 16777216.0f32))
        (#assert (#f32::eq runtimeRounded runtimeRounded))
        (#assert (#f32::eq runtimeRounded 0.0f32))
        (#assert (#f64::eq forward 2.0f64))
        (#assert (#f64::ne nan nan))
        (#assert (#f64::eq infinity (#f64::div 1.0f64 0.0f64)))
        (#assert (#f64::lt (#f64::div 1.0f64 negativeZero) 0.0f64))
        (#unsafe (#block
          (#assert (#f64::eq (#get pair large) forward))
          (#assert (#f64::eq (#index values 1) infinity))))
        (#return 42u64))";
    fs::write(root.join("main.lim"), source).unwrap();
    let result = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(root.join("main.lim"))
            .arg("-o")
            .arg(root.join("program")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(result.0.success(), "{}", String::from_utf8_lossy(&result.2));
    assert_eq!(
        support::run(
            &mut Command::new(root.join("program")),
            Duration::from_secs(2),
            1024
        )
        .unwrap()
        .0
        .code(),
        Some(42)
    );
    for invalid in [
        "(#const a #f64 b) (#const b #f64 a)",
        "(#fn value () #f64 (#return 1.0f64)) (#const a #f64 (#call value ()))",
    ] {
        let error = lim::compile_source_to_assembly(
            invalid,
            &root.join("bad.lim"),
            &lim::CompileConfig::default(),
            &root.join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.span.is_some());
    }
}
