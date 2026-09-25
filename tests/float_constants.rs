mod support;
use std::{fs, process::Command, time::Duration};

#[test]
fn floating_globals_preserve_width_bits_and_runtime_semantics() {
    let scratch = support::Scratch::new("float-constants");
    let root = scratch.path();
    let source = "
      (#const Rounded f32 (#f32.- (#f32.+ 16777216.0f32 1.0f32) 16777216.0f32))
      (#const Forward f64 (#f64.+ Base 0.5f64))
      (#const Base f64 1.5f64)
      (#const NegativeZero f64 -0.0f64)
      (#const Infinity f64 (#f64./ 1.0f64 0.0f64))
      (#const Nan f64 (#f64./ 0.0f64 0.0f64))
      (#struct Floats ((small f32) (large f64)))
      (#static Pair Floats (#struct-literal Floats ((large Forward) (small Rounded))))
      (#static Values (#array f64 2) (#array-of (#array f64 2) NegativeZero Infinity))
      (#fn main () u64
        (#let rounded f32 (#f32.- (#f32.+ 16777216.0f32 1.0f32) 16777216.0f32))
        (#assert (#f32.== Rounded rounded))
        (#assert (#f32.== Rounded 0.0f32))
        (#assert (#f64.== Forward 2.0f64))
        (#assert (#f64.!= Nan Nan))
        (#assert (#f64.== Infinity (#f64./ 1.0f64 0.0f64)))
        (#assert (#f64.< (#f64./ 1.0f64 NegativeZero) 0.0f64))
        (#unsafe (#block
          (#assert (#f64.== (#get Pair large) Forward))
          (#assert (#f64.== (#index Values 1) Infinity))))
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
        "(#const A f64 B) (#const B f64 A)",
        "(#fn value () f64 (#return 1.0f64)) (#const A f64 (#call value (#fn-args)))",
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
