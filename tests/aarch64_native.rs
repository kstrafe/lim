mod support;
use std::{fs, os::unix::process::ExitStatusExt, process::Command, time::Duration};

const TARGET: lim::TargetDescription = lim::TargetDescription::AARCH64_LINUX;

fn assembly(source: &str) -> String {
    let program = lim::parse_program(source).unwrap();
    lim::generate_assembly_for_target(&program, TARGET)
        .unwrap_or_else(|error| panic!("{error}\n{source}"))
}

fn run(source: &str) -> std::process::ExitStatus {
    run_assembly(assembly(source))
}

fn run_assembly(assembly: String) -> std::process::ExitStatus {
    // Required execution coverage: never silently skip an absent emulator.
    let version = Command::new("qemu-aarch64")
        .arg("--version")
        .output()
        .expect("qemu-aarch64 is required; run these tests inside nix develop");
    assert!(version.status.success());
    let scratch = support::Scratch::new("aarch64-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], TARGET).unwrap();
    let bytes = fs::read(&binary).unwrap();
    assert_eq!(u16::from_le_bytes(bytes[18..20].try_into().unwrap()), 183);
    let (status, out, err) = support::run(
        &mut Command::new("qemu-aarch64")
            .arg(binary)
            .current_dir(scratch.path()),
        Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert!(out.is_empty(), "unexpected stdout: {out:?}");
    if status.success() || status.code().is_some() {
        assert!(err.is_empty(), "unexpected stderr: {err:?}");
    }
    status
}

fn returns(source: &str, expected: i32) {
    assert_eq!(run(source).code(), Some(expected), "{source}");
}

#[test]
fn explicitly_proven_index_executes_and_omits_bounds_traps() {
    returns(include_str!("../examples/index_contracts.lim"), 42);
    returns(include_str!("../examples/generated_array.lim"), 42);
    returns(include_str!("../examples/surface_syntax.lim"), 42);
    let source = r#"
#fn read {
  #params = ((values (#ref (#array #u64 4))) (index #usize));
  #returns = #u64;
  #body = (
          (#requires (#usize::lt index 4usize)) (#return (#index-proven values index))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let values (#array #u64 4) (#array (#array #u64 4) 1u64 42u64 3u64 4u64))
          (#let index #usize 1usize) (#assume (#usize::lt index 4usize))
          (#return (#call read ((values (#borrow values)) (index index))))
  );
}
"#;
    let proven = assembly(source);
    let checked = assembly(&source.replace("#index-proven", "#index"));
    assert!(proven.matches("brk").count() < checked.matches("brk").count());
    let mut config = lim::CompileConfig::default();
    config.set("contracts", "check");
    let program = lim::parse_program_with_config(source, &config).unwrap();
    let audited = lim::generate_assembly_for_target(&program, TARGET).unwrap();
    assert!(audited.matches("brk").count() > proven.matches("brk").count());
    assert_eq!(run_assembly(audited).code(), Some(42));
    let invalid = source
        .replace("#requires", "#assume")
        .replace("#usize 1usize", "#usize 4usize");
    let program = lim::parse_program_with_config(&invalid, &config).unwrap();
    let audited = lim::generate_assembly_for_target(&program, TARGET).unwrap();
    assert_eq!(run_assembly(audited).signal(), Some(5));
}

#[test]
fn scalar_arithmetic_width_signedness_and_control_flow_execute() {
    returns("#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n", 42);
    returns(
        "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#let-mut sum #u64 0u64) (#let-mut i #u64 0u64)
        (#while (#u64::lt i 7u64) (#set sum (#u64::add-wrap sum i)) (#set i (#u64::add-wrap i 1u64)))
        (#return (#u64::mul-wrap sum 2u64))\n  );\n}\n",
        42,
    );
    returns(
        "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#assert (#i8::eq (#i8::add-wrap 127i8 1i8) -128i8))
        (#assert (#u8::eq (#u8::add-wrap 255u8 1u8) 0u8))
        (#assert (#i64::lt -9i64 2i64))
        (#assert (#u64::gt 18446744073709551615u64 2u64))
        (#assert (#i64::eq (#i64::div-wrap -21i64 2i64) -10i64))
        (#assert (#i64::eq (#i64::rem-wrap -21i64 2i64) -1i64))
        (#assert (#u64::eq (#u64::div-wrap 18446744073709551615u64 3u64) 6148914691236517205u64))
        (#return (#if (#bool::and true (#bool::not false)) 42u64 0u64))\n  );\n}\n",
        42,
    );
}

#[test]
fn scalar_register_stack_boundaries_and_nested_calls_execute() {
    returns(
        "#fn sum {
  #params = ((a #u64) (b #u64) (c #u64) (d #u64) (e #u64)
        (f #u64) (g #u64) (h #u64) (i #u64) (j #u64));
  #returns = #u64;
  #body = (
        (#return (#u64::add-wrap (#u64::add-wrap a i) j))
  );
}
#fn add {
  #params = ((left #u64) (right #u64));
  #returns = #u64;
  #body = ( (#return (#u64::add-wrap left right))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return (#call sum ((j (#call add ((left 10u64) (right 12u64))))
          (i 19u64) (a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64) (f 6u64) (g 7u64) (h 8u64))))\n  );\n}\n",
        42,
    );
}

#[test]
fn aggregates_functions_mutation_and_pattern_bindings_execute() {
    returns(
        "#struct Value () ((tag #u64) (items (#array #u64 6)) (pair (#tuple #u64 #u64)))
#fn make {
  #params = ((n #u64));
  #returns = Value;
  #body = ( (#return (#struct-literal Value
          ((pair (#tuple (#tuple #u64 #u64) n 2u64)) (tag 9u64)
           (items (#array-of (#array #u64 6) 1u64 2u64 3u64 4u64 5u64 6u64)))))
  );
}
#fn pass {
  #params = ((value Value));
  #returns = Value;
  #body = ( (#return value)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut value Value (#call pass ((value (#call make ((n 40u64)))))))
          (#let (#tuple left right) (#tuple #u64 #u64) (#get value pair))
          (#set-field value tag (#u64::add-wrap left right))
          (#assert (#u64::eq (#index (#get value items) 5usize) 6u64))
          (#return (#get value tag))\n  );\n}\n",
        42,
    );
    returns(
        "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#let-mut values (#array #u64 3) (#array-of (#array #u64 3) 1u64 2u64 3u64))
        (#set-index values 1usize 42u64) (#return (#index values 1usize))\n  );\n}\n",
        42,
    );
}

#[test]
fn references_exclusive_moves_and_aggregate_reference_returns_execute() {
    returns(include_str!("../examples/exclusive_reference_move.lim"), 42);
    returns(include_str!("../examples/reference_parent_call.lim"), 42);
    returns(include_str!("../examples/reference_assignment.lim"), 42);
    returns(
        "#struct Views () ((value (#ref #u64)))
#fn lend {
  #params = ((owner (#ref #u64)));
  #returns = Views;
  #body = ( (#return (#struct-literal Views ((value owner))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let owner #u64 42u64)
          (#let views Views (#call lend ((owner (#borrow owner)))))
          (#return (#deref (#get views value)))\n  );\n}\n",
        42,
    );
    returns("#struct Pair () ((left #u64) (right #u64))
#fn replace {
  #params = ((target (#ref-mut Pair)) (value Pair));
  #returns = ();
  #body = ( (#deref-set target value) (#return ())
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut owner Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
          (#call replace ((target (#borrow-mut owner)) (value (#struct-literal Pair ((left 40u64) (right 2u64))))))
          (#return (#u64::add-wrap (#get owner left) (#get owner right)))\n  );\n}\n",42);
}

#[test]
fn enum_match_let_else_guards_and_loop_values_execute() {
    returns(
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#fn choose {
  #params = ((value Maybe));
  #returns = #u64;
  #body = (
          (#return (#match value (#case (Maybe.Some n) (#when (#u64::gt n 40u64)) n)
            (#case (Maybe.Some _) 0u64) (#case Maybe.None 0u64)))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-else (Maybe.Some n) Maybe (Maybe.Some 42u64) (#return 0u64))
          (#return (#call choose ((value (Maybe.Some n)))))\n  );\n}\n",
        42,
    );
    returns(
        "#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut n #u64 0u64)
        (#return (#loop (#set n (#u64::add-wrap n 1u64))
          (#if (#u64::eq n 42u64) (#block (#break n)) ())))\n  );\n}\n",
        42,
    );
}

#[test]
fn invalid_runtime_operations_fault_instead_of_returning_a_value() {
    for source in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let zero #u64 0u64) (#return (#u64::div-wrap 42u64 zero))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let shift #u64 64u64) (#return (#u64::shl 1u64 shift))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let i #usize 3usize) (#let a (#array #u64 2) (#array-of (#array #u64 2) 1u64 2u64)) (#return (#index a i))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#assert false) (#return 42u64)\n  );\n}\n",
    ] { assert_eq!(run(source).code(),None,"{source}"); }
}

#[test]
fn fixed_frame_stack_bound_and_large_offsets_are_supported() {
    let source = "#fn value {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut a (#array #u64 5000) (#array-repeat 0u64))
          (#set-index a 4999usize (#call value ())) (#return (#index a 4999usize))\n  );\n}\n";
    let listing = assembly(source);
    let report = lim::aarch64::stack_usage_report(&listing).unwrap();
    assert!(report.contains("incoming SP"));
    assert!(report.contains("saved FP/LR"));
    returns(source, 42);
    assert!(lim::aarch64::stack_usage_report("x86 assembly").is_err());
    assert!(lim::aarch64::stack_usage_report(
        "// lim-aarch64-v1\n.text\n// lim-frame main 16 main\n"
    )
    .is_err());
}

#[test]
fn unsupported_primitives_fail_closed_and_link_failures_preserve_output() {
    for source in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let f #f64 1.0f64) (#return 42u64)\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let n #u128 1u128) (#return 42u64)\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64::add-saturate 40u64 2u64))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#unsafe (#asm #u64 () \"mov x0, #42\")))\n  );\n}\n",
    ] {
        let program = lim::parse_program(source).unwrap();
        let error = lim::generate_assembly_for_target(&program, TARGET).unwrap_err();
        assert!(
            error.contains("AArch64 Linux backend does not support"),
            "{error}"
        );
    }
    let scratch = support::Scratch::new("aarch64-link-failure");
    let output = scratch.path().join("program");
    fs::write(&output, b"existing").unwrap();
    let listing = assembly("#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n");
    assert!(lim::link_native_binary(&listing, &output, &[], &["c".into()], TARGET).is_err());
    assert_eq!(fs::read(&output).unwrap(), b"existing");
    assert!(lim::aarch64::executable(".inst 0xd65f03c0").is_err());
}

#[test]
fn ownership_rejections_still_run_the_shared_semantic_gate() {
    for source in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let-mut owner #u64 42u64) (#let view (#ref #u64) (#borrow owner)) (#set owner 1u64) (#return (#deref view))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let-mut owner #u64 42u64) (#let view (#ref-mut #u64) (#borrow-mut owner)) (#drop view) (#return (#deref view))\n  );\n}\n",
    ] {
        let program = lim::parse_program(source).unwrap();
        assert!(lim::generate_assembly_for_target(&program,TARGET).is_err());
    }
}

#[test]
fn native_aarch64_syscalls_and_explicit_target_cfg_execute_through_cli() {
    let scratch = support::Scratch::new("aarch64-syscalls");
    let source = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    let source_text = format!("#cfg-if (#cfg-and (#cfg-is #arch aarch64) (#cfg-is #os linux)
        (#cfg-is #target aarch64-unknown-linux-gnu)) ({}) (#cfg-else (#fn main {{
          #params = ();
          #returns = #u64;
          #body = ( (#return missing)\n          );\n        }}))\n",
      include_str!("../examples/aarch64_syscall.lim"));
    fs::write(&source, source_text).unwrap();
    let compiled = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&source)
        .args(["--target", "aarch64-linux", "-o"])
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let (status, out, err) = support::run(
        &mut Command::new("qemu-aarch64")
            .arg(&binary)
            .current_dir(scratch.path()),
        Duration::from_secs(5),
        4096,
    )
    .expect("qemu-aarch64 is required inside nix develop");
    assert_eq!(status.code(), Some(42));
    assert_eq!(out, b"*");
    assert!(err.is_empty());
    let report = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--stack-usage")
        .arg(&source)
        .args(["--target", "aarch64-linux"])
        .output()
        .unwrap();
    assert!(
        report.status.success(),
        "{}",
        String::from_utf8_lossy(&report.stderr)
    );
    assert!(String::from_utf8_lossy(&report.stdout).contains("AArch64"));
}

#[test]
fn unsupported_codegen_errors_include_the_offending_source_line() {
    let scratch = support::Scratch::new("aarch64-diagnostics");
    let source = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    for text in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n    (#return (#u64::add-saturate 40u64 2u64))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n    (#let f #f64 1.0f64)\n    (#return 42u64)\n  );\n}\n",
    ] {
        fs::write(&source, text).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .args(["--target", "aarch64-linux", "-o"])
            .arg(&binary)
            .output()
            .unwrap();
        assert!(!output.status.success());
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(error.contains("error[E5000]"), "{error}");
        assert!(error.contains("2 |"), "{error}");
        assert!(error.contains("^"), "{error}");
        assert!(!binary.exists());
    }
}

#[test]
fn shipped_scalar_and_ownership_examples_execute() {
    returns(include_str!("../examples/aarch64_scalar.lim"), 42);
    returns(include_str!("../examples/aarch64_ownership.lim"), 42);
}

#[test]
fn oversized_layouts_and_unsupported_pointer_operations_return_diagnostics() {
    for source in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let a (#array #u64 2097153) (#array-repeat 0u64)) (#return 42u64)\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let a (#array () 2097153) (#array-repeat ())) (#return 42u64)\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let-mut a #u64 42u64) (#let p (#ptr #u64) (#unsafe (#addr-of a))) (#return 42u64)\n  );\n}\n",
    ] {
        let program = lim::parse_program(source).unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            lim::generate_assembly_for_target(&program,TARGET)));
        assert!(result.is_ok(),"source must yield a diagnostic, not panic");
        assert!(result.unwrap().is_err());
    }
}
