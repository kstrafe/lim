//! Verify the published ELF, not just the absence of source FFI declarations.
use std::{fs, path::Path, process::Command, time::Duration};

mod support;
use support::elf_fixture as fixture;

fn inspect(binary: &Path, options: &[&str]) -> String {
    let output = Command::new("readelf")
        .args(options)
        .arg(binary)
        .env("LC_ALL", "C")
        .output()
        .expect("read ELF metadata");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

fn assert_static(binary: &Path) {
    assert!(!inspect(binary, &["-lW"]).contains("INTERP"));
    assert!(!inspect(binary, &["-dW"]).contains("(NEEDED)"));
    assert!(inspect(binary, &["-dW"]).contains("There is no dynamic section"));
}

fn assert_runs(binary: &Path, stdout: &[u8]) {
    let (status, actual, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert_eq!(actual, stdout);
    assert!(stderr.is_empty());
}

fn compile(source: &str, directory: &Path, libraries: &[String]) -> std::path::PathBuf {
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        source,
        &directory.join("input.lim"),
        &lim::CompileConfig::default(),
        &directory.join("cache"),
        target,
    )
    .unwrap();
    let binary = directory.join("program");
    lim::link_native_binary(&assembly, &binary, &[], libraries, target).unwrap();
    binary
}

#[test]
fn referenced_tuple_fields_keep_layout_direction_and_evaluate_receivers_once() {
    let scratch = support::Scratch::new("reference-tuple-getters");
    for (ty, borrow) in [
        ("#ref", "#borrow"),
        ("#ref-mut", "#borrow-mut"),
        ("#pin-ref", "#pin-borrow"),
        ("#pin-ref-mut", "#pin-borrow-mut"),
    ] {
        let tuple = "(#tuple () #u128 #f64 #u64)";
        let source = format!(
            "(#fn receiver (: view ({ty} {tuple}) : count (#ref-mut #u64)) ({ty} {tuple})
              (#deref-set count (#u64.+.wrap (#deref count) 1u64)) (#return view))
              (#fn main () #u64
                (#let-mut values {tuple} (#tuple {tuple} () 18446744073709551617u128 3.5f64 42u64))
                (#let view ({ty} {tuple}) ({borrow} values)) (#let-mut count #u64 0u64)
                (#let unit () (#get (#call receiver (: view view : count (#borrow-mut count))) 0))
                (#assert (#u64.== count 1u64))
                (#assert (#u128.== (#get view 1) 18446744073709551617u128))
                (#assert (#f64.== (#get view 2) 3.5f64))
                (#return (#get view 3)))"
        );
        assert_runs(&compile(&source, scratch.path(), &[]), b"");
    }
    for (ty, borrow) in [("#ref", "#borrow"), ("#pin-ref", "#pin-borrow")] {
        let tuple = "(#tuple #u128 #f64 #u64)";
        let source = format!(
            "(#let Values {tuple} (#tuple {tuple} 18446744073709551617u128 3.5f64 42u64))
              (#fn main () #u64 (#let view ({ty} {tuple}) ({borrow} Values))
                (#assert (#u128.== (#get view 0) 18446744073709551617u128))
                (#assert (#f64.== (#get view 1) 3.5f64)) (#return (#get view 2)))"
        );
        assert_runs(&compile(&source, scratch.path(), &[]), b"");
    }
}

#[test]
fn simple_lim_program_builds_with_no_external_tools_on_path() {
    let scratch = support::Scratch::new("internal-fibonacci-link");
    let source = scratch.path().join("fibonacci.lim");
    let binary = scratch.path().join("fibonacci");
    fs::write(&source, include_str!("../examples/fibonacci.lim")).unwrap();
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    assert_static(&binary);
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(55));
}

#[test]
fn loop_headers_and_outer_value_transfers_return_the_selected_value() {
    let scratch = support::Scratch::new("value-loop-phase-targets");
    for statement in [
        "(#while (#block (#break 42u64) false) ())",
        "(#for (#let count #u64 (#block (#break 42u64) 0u64)) false () ())",
        "(#for () (#block (#break 42u64) false) () ())",
        "(#for () true (#break 42u64) ())",
        "(#while true (#break-to outer 42u64))",
        "(#loop (#break-to outer 42u64))",
        "(#for () true () (#break-to outer 42u64))",
    ] {
        let source = format!(
            "(#fn main () #u64 (#return (#label outer (#loop {statement} (#break 0u64)))))"
        );
        assert_runs(&compile(&source, scratch.path(), &[]), b"");
    }
}

#[test]
fn labeled_value_loops_reserve_scratch_for_large_patterns_and_projections() {
    let scratch = support::Scratch::new("labeled-loop-aggregate-scratch");
    let array = "(#array-of (#array #u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64)";
    for expression in [
        format!(
            "(#label outer (#loop
          (#let-else (#array a b c d e f answer) (#array #u64 7) {array} (#unreachable))
          (#break-to outer answer)))"
        ),
        format!(
            "(#label outer (#loop
          (#break-to outer (#index (#index
            (#array-of (#array (#array #u64 7) 1) {array}) 0usize) 6usize))))"
        ),
        format!(
            "(#loop
          (#break (#index (#index
            (#array-of (#array (#array #u64 7) 1) {array}) 0usize) 6usize)))"
        ),
    ] {
        let source = format!("(#fn main () #u64 (#return {expression}))");
        assert_runs(&compile(&source, scratch.path(), &[]), b"");
    }
}

#[test]
fn large_loop_results_keep_their_local_or_indirect_destination() {
    let scratch = support::Scratch::new("large-loop-result-destinations");
    let values = "(#array-of (#array #u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64)";
    // The label is the final value of a block, not a statement-only loop.
    // A break in the nested loop must use the outer loop's destination.
    let result = format!(
        "(#block (#label outer (#loop
      (#let unused #u64 0u64) (#forget unused)
      (#loop (#break-to outer {values})))))"
    );
    for source in [
        format!(
            "(#fn main () #u64
          (#let values (#array #u64 7) {result})
          (#return (#index values 6usize)))"
        ),
        format!(
            "(#enum Packet () (: Present (#array #u64 7)))
          (#fn main () #u64
            (#let packet Packet (#block (#label outer (#loop
              (#forget 0u64) (#break-to outer (Present {values}))))))
            (#let-else (Present values) Packet packet (#unreachable))
            (#return (#index values 6usize)))"
        ),
        // The loop writes a nested field at a nonzero offset in an indirect
        // return. Accidentally writing at zero corrupts the sentinel field.
        format!(
            "(#struct Packet () (: sentinel #u64 : values (#array #u64 7)))
          (#fn make () Packet (#return (#struct-literal Packet
            (: sentinel 9u64 : values {result}))))
          (#fn main () #u64 (#let packet Packet (#call make (:)))
            (#assert (#u64.== (#get packet sentinel) 9u64))
            (#return (#index (#get packet values) 6usize)))"
        ),
    ] {
        assert_runs(&compile(&source, scratch.path(), &[]), b"");
    }
}

#[test]
fn constant_data_and_rip_relative_loads_build_without_external_tools() {
    let scratch = support::Scratch::new("internal-constant-link");
    for (name, source) in [
        ("global", include_str!("../examples/global.lim")),
        ("global_128", include_str!("../examples/global_128.lim")),
    ] {
        let input = scratch.path().join(format!("{name}.lim"));
        let binary = scratch.path().join(name);
        fs::write(&input, source).unwrap();
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_static(&binary);
        assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
    }
}

#[test]
fn source_constants_reside_in_a_nonexecutable_read_only_load_segment() {
    let scratch = support::Scratch::new("native-read-only-segment");
    let assembly = ".intel_syntax noprefix\n.section .rodata\n.align 8\nconstant:\n.quad 42\n.text\n.globl main\nmain:\n mov rax, QWORD PTR [rip+constant]\n ret\n";
    for (name, libraries) in [("static", vec![]), ("dynamic", vec!["c".to_owned()])] {
        let binary = scratch.path().join(name);
        lim::link_native_binary(
            assembly,
            &binary,
            &[],
            &libraries,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
        let bytes = fs::read(&binary).unwrap();
        let header_offset = u64::from_le_bytes(bytes[32..40].try_into().unwrap()) as usize;
        let header_size = u16::from_le_bytes(bytes[54..56].try_into().unwrap()) as usize;
        let header_count = u16::from_le_bytes(bytes[56..58].try_into().unwrap()) as usize;
        let loads = (0..header_count)
            .filter_map(|index| {
                let header = header_offset + index * header_size;
                (u32::from_le_bytes(bytes[header..header + 4].try_into().unwrap()) == 1).then(
                    || {
                        (
                            u32::from_le_bytes(bytes[header + 4..header + 8].try_into().unwrap()),
                            u64::from_le_bytes(bytes[header + 16..header + 24].try_into().unwrap()),
                        )
                    },
                )
            })
            .collect::<Vec<_>>();
        assert!(loads.contains(&(5, 0x400000)), "{name}: {loads:?}");
        assert!(loads.contains(&(4, 0x08400000)), "{name}: {loads:?}");
        assert_eq!(
            loads.iter().any(|(flags, _)| *flags == 6),
            name == "dynamic"
        );
        assert!(!loads.iter().any(|(flags, _)| *flags == 7));
    }
}

#[test]
fn object_rodata_relocations_resolve_into_the_read_only_segment() {
    let scratch = support::Scratch::new("object-read-only-segment");
    let object = scratch.path().join("constant.o");
    let code = [0x48, 0x8b, 0x05, 0, 0, 0, 0, 0xc3];
    fs::write(
        &object,
        fixture::object(
            &[
                fixture::Section {
                    name: ".text",
                    bytes: &code,
                    size: code.len(),
                    writable: false,
                    executable: true,
                },
                fixture::Section {
                    name: ".rodata",
                    bytes: &42u64.to_le_bytes(),
                    size: 8,
                    writable: false,
                    executable: false,
                },
            ],
            &[
                fixture::Symbol {
                    name: "read_constant",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "constant",
                    section: Some(1),
                    value: 0,
                    global: false,
                },
            ],
            &[fixture::Relocation {
                section: 0,
                offset: 3,
                symbol: 1,
                kind: 2,
                addend: -4,
            }],
        ),
    )
    .unwrap();
    let program = lim::parse_program(
        "(#extern-fn #abi-c read_constant () #u64) (#fn main () #u64 (#return (#unsafe (#unsafe-call read_constant (:)))))",
    )
    .unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[object],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_static(&binary);
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
    let segments = inspect(&binary, &["-lW"]);
    assert!(
        segments
            .lines()
            .any(|line| line.contains("LOAD") && line.contains(" R  ")),
        "{segments}"
    );
}

#[test]
fn array_indexing_builds_without_external_tools() {
    let scratch = support::Scratch::new("internal-array-link");
    for (name, source, expected) in [
        ("array", include_str!("../examples/array.lim"), 41),
        (
            "array_repeat",
            include_str!("../examples/array_repeat.lim"),
            13,
        ),
        ("array-of", include_str!("../examples/array-of.lim"), 30),
    ] {
        let input = scratch.path().join(format!("{name}.lim"));
        let binary = scratch.path().join(name);
        fs::write(&input, source).unwrap();
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_static(&binary);
        assert_eq!(
            Command::new(&binary).status().unwrap().code(),
            Some(expected)
        );
    }
}

#[test]
fn aggregate_memory_operands_build_without_external_tools() {
    let scratch = support::Scratch::new("internal-aggregate-link");
    for (name, source, expected) in [
        (
            "aggregate_let",
            include_str!("../examples/aggregate_let.lim"),
            4,
        ),
        (
            "aggregate_match_return",
            include_str!("../examples/aggregate_match_return.lim"),
            20,
        ),
        (
            "array_return_index",
            include_str!("../examples/array_return_index.lim"),
            20,
        ),
        (
            "const_aggregate",
            include_str!("../examples/const_aggregate.lim"),
            42,
        ),
    ] {
        let input = scratch.path().join(format!("{name}.lim"));
        let binary = scratch.path().join(name);
        fs::write(&input, source).unwrap();
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_static(&binary);
        assert_eq!(
            Command::new(&binary).status().unwrap().code(),
            Some(expected)
        );
    }
}

#[test]
fn scalar_and_task_programs_build_without_external_tools() {
    let scratch = support::Scratch::new("internal-scalar-link");
    for (name, source) in [
        ("bitwise_not", include_str!("../examples/bitwise_not.lim")),
        ("bool_bitwise", include_str!("../examples/bool_bitwise.lim")),
        (
            "constant_short_circuit",
            include_str!("../examples/constant_short_circuit.lim"),
        ),
        (
            "cooperative_tasks",
            include_str!("../examples/cooperative_tasks.lim"),
        ),
        (
            "allocator_state",
            include_str!("../examples/allocator_state.lim"),
        ),
    ] {
        let input = scratch.path().join(format!("{name}.lim"));
        let binary = scratch.path().join(name);
        let task_library = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("library/tasks.lim")
            .to_string_lossy()
            .into_owned();
        fs::write(
            &input,
            source
                .replace("../library/tasks.lim", &task_library)
                .replace(
                    "../library/cell.lim",
                    &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
                ),
        )
        .unwrap();
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_static(&binary);
        assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
    }
}

#[test]
fn syscall_echo_builds_without_external_tools() {
    use std::io::Write;
    let scratch = support::Scratch::new("internal-syscall-echo");
    let input = scratch.path().join("echo_input.lim");
    let binary = scratch.path().join("echo_input");
    let library = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("library/linux_x86_64.lim")
        .to_string_lossy()
        .into_owned();
    fs::write(
        &input,
        include_str!("../examples/echo_input.lim").replace("../library/linux_x86_64.lim", &library),
    )
    .unwrap();
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    assert_static(&binary);
    let mut child = Command::new(&binary)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"A\0\xff\n").unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"A\0\xff\n");
}

#[test]
fn unreachable_branch_traps_with_internal_encoding() {
    use std::os::unix::process::ExitStatusExt;
    let scratch = support::Scratch::new("internal-unreachable");
    let input = scratch.path().join("never.lim");
    let binary = scratch.path().join("never");
    fs::write(&input, include_str!("../examples/never.lim")).unwrap();
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    for _ in 0..32 {
        let (status, stdout, stderr) =
            support::run(&mut Command::new(&binary), Duration::from_secs(2), 1024).unwrap();
        assert_eq!(status.signal(), Some(4));
        assert!(stdout.is_empty());
        assert!(stderr.is_empty());
    }
}

#[test]
fn scalar_float_programs_build_without_external_tools() {
    let scratch = support::Scratch::new("internal-float-link");
    for (name, source, expected) in [
        ("float", include_str!("../examples/float.lim"), 42),
        ("float32", include_str!("../examples/float32.lim"), 42),
        (
            "float_control",
            include_str!("../examples/float_control.lim"),
            42,
        ),
        (
            "float_global_expr",
            include_str!("../examples/float_global_expr.lim"),
            42,
        ),
        (
            "float_comparison_edges",
            include_str!("../examples/float_comparison_edges.lim"),
            42,
        ),
        (
            "mixed_float",
            include_str!("../examples/mixed_float.lim"),
            0,
        ),
    ] {
        let input = scratch.path().join(format!("{name}.lim"));
        let binary = scratch.path().join(name);
        fs::write(&input, source).unwrap();
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_static(&binary);
        assert_eq!(
            Command::new(&binary).status().unwrap().code(),
            Some(expected)
        );
    }
}

#[test]
fn linux_aio_builds_and_runs_without_external_tools() {
    let scratch = support::Scratch::new("internal-linux-aio");
    let input = scratch.path().join("linux_aio.lim");
    let binary = scratch.path().join("linux_aio");
    let library = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("library/linux_x86_64.lim")
        .to_string_lossy()
        .into_owned();
    fs::write(
        &input,
        include_str!("../examples/linux_aio.lim").replace("../library/linux_x86_64.lim", &library),
    )
    .unwrap();
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    assert_static(&binary);
    let (status, stdout, stderr) = support::run(
        &mut Command::new(&binary).current_dir(scratch.path()),
        Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/aio.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn generated_kernel_threads_and_atomics_build_without_external_tools() {
    let scratch = support::Scratch::new("internal-kernel-threads");
    let library = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("library/linux_x86_64.lim")
        .to_string_lossy()
        .into_owned();
    for (name, source, expected_stdout) in [
        (
            "kernel_threads",
            include_str!("../examples/kernel_threads.lim"),
            b"T\n".as_slice(),
        ),
        (
            "atomic_claim",
            include_str!("../examples/atomic_claim.lim"),
            b"".as_slice(),
        ),
    ] {
        let input = scratch.path().join(format!("{name}.lim"));
        let binary = scratch.path().join(name);
        fs::write(
            &input,
            source.replace("../library/linux_x86_64.lim", &library),
        )
        .unwrap();
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_static(&binary);
        for _ in 0..8 {
            let (status, stdout, stderr) =
                support::run(&mut Command::new(&binary), Duration::from_secs(5), 4096).unwrap();
            assert_eq!(status.code(), Some(42), "{name}: {stderr:?}");
            assert_eq!(stdout, expected_stdout, "{name}");
            assert!(stderr.is_empty());
        }
    }
}

#[test]
fn syscall_library_binary_has_no_interpreter_or_dynamic_dependencies() {
    let scratch = support::Scratch::new("syscall-static-link");
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/linux_x86_64.lim");
    let source = format!(
        "(#import {:?}) (#fn main () #u64
          (#let letter #u8 83u8)
          (#assert (#i64.== (#call linux-write-byte (: source (#borrow letter))) 1i64))
          (#return 42u64))",
        library.to_str().unwrap()
    );
    let binary = compile(&source, scratch.path(), &[]);
    assert_static(&binary);
    assert_runs(&binary, b"S");
}

#[test]
fn unused_external_declarations_do_not_require_a_c_runtime() {
    let scratch = support::Scratch::new("unused-extern-link");
    let binary = compile(
        "(#extern-fn #abi-c abs ((value #i32)) #i32)
         (#fn main () #u64 (#return 42u64))",
        scratch.path(),
        &[],
    );
    assert_static(&binary);
    assert_runs(&binary, b"");
}

#[test]
fn referenced_foreign_functions_still_link_and_run() {
    let scratch = support::Scratch::new("foreign-link");
    let source = include_str!("../examples/extern_abs.lim");
    let binary = compile(source, scratch.path(), &[]);
    assert!(inspect(&binary, &["-lW"]).contains("INTERP"));
    assert!(inspect(&binary, &["-dW"]).contains("libc.so"));
    assert_runs(&binary, b"");
}

#[test]
fn dynamic_images_are_reproducible_and_keep_code_nonwritable() {
    let scratch = support::Scratch::new("dynamic-elf-reproducible");
    let source = include_str!("../examples/extern_abs.lim");
    let program = lim::parse_program(source).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let first = scratch.path().join("first");
    let second = scratch.path().join("second");
    for output in [&first, &second] {
        lim::link_native_binary(
            &assembly,
            output,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
    }
    assert_eq!(fs::read(&first).unwrap(), fs::read(&second).unwrap());
    let headers = inspect(&first, &["-lW"]);
    assert!(headers.contains("INTERP"), "{headers}");
    assert!(
        headers
            .lines()
            .any(|line| line.contains("LOAD") && line.contains("R E")),
        "{headers}"
    );
    assert!(
        headers
            .lines()
            .any(|line| line.contains("LOAD") && line.contains("RW ")),
        "{headers}"
    );
    assert!(
        !headers
            .lines()
            .any(|line| line.contains("LOAD") && line.contains("RWE")),
        "{headers}"
    );
    assert_runs(&first, b"");
}

#[test]
fn missing_foreign_symbol_preserves_existing_binary() {
    let scratch = support::Scratch::new("missing-foreign-symbol");
    let binary = compile("(#fn main () #u64 (#return 42u64))", scratch.path(), &[]);
    let original = fs::read(&binary).unwrap();
    let program = lim::parse_program(
        "(#extern-fn #abi-c lim_symbol_that_does_not_exist () #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call lim_symbol_that_does_not_exist (:)))))"
    ).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let error = lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("lim_symbol_that_does_not_exist"),
        "{error:?}"
    );
    assert_eq!(fs::read(&binary).unwrap(), original);

    let input = scratch.path().join("missing.lim");
    fs::write(&input,
        "(#extern-fn #abi-c lim_symbol_that_does_not_exist () #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call lim_symbol_that_does_not_exist (:)))))\n"
    ).unwrap();
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(scratch.path().join("missing"))
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(!compilation.status.success());
    let diagnostic = String::from_utf8_lossy(&compilation.stderr);
    assert!(diagnostic.contains("missing.lim:2:"), "{diagnostic}");
    assert!(
        diagnostic.contains("#call lim_symbol_that_does_not_exist"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains('^'), "{diagnostic}");
}

#[test]
fn inline_assembly_external_references_are_detected_from_the_object() {
    let scratch = support::Scratch::new("assembly-foreign-link");
    // No .extern directive: the object relocation is authoritative.
    let assembly = ".intel_syntax noprefix\n.text\n.globl main\nmain:\n sub rsp, 8\n mov edi, -42\n call abs\n add rsp, 8\n ret\n.section .note.GNU-stack,\"\",@progbits\n";
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_runs(&binary, b"");
    assert!(inspect(&binary, &["-dW"]).contains("libc.so"));
}

#[test]
fn explicitly_requested_libraries_are_not_ignored() {
    let scratch = support::Scratch::new("explicit-library-link");
    let binary = compile(
        "(#fn main () #u64 (#return 42u64))",
        scratch.path(),
        &["m".into()],
    );
    assert_runs(&binary, b"");
    let input = scratch.path().join("explicit.lim");
    fs::write(&input, "(#fn main () #u64 (#return 42u64))").unwrap();
    let tool_free = scratch.path().join("tool-free-m");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&tool_free)
        .arg("--link-lib")
        .arg("m")
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    assert!(inspect(&tool_free, &["-dW"]).contains("libm.so"));
    assert_runs(&tool_free, b"");
    // Missing explicit libraries must still fail without replacing an output.
    let original = fs::read(&binary).unwrap();
    let program = lim::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    assert!(lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &["lim_missing_native_link_test".into()],
        lim::TargetDescription::X86_64_SYSTEM_V
    )
    .is_err());
    assert_eq!(fs::read(binary).unwrap(), original);
}

#[test]
fn supplied_object_references_are_inspected_too() {
    let scratch = support::Scratch::new("supplied-object-link");
    let object = scratch.path().join("helper.o");
    fs::write(
        &object,
        fixture::object(
            &[fixture::Section {
                name: ".text",
                bytes: &[0xe9, 0, 0, 0, 0],
                size: 5,
                writable: false,
                executable: true,
            }],
            &[
                fixture::Symbol {
                    name: "helper",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "abs",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[fixture::Relocation {
                section: 0,
                offset: 1,
                symbol: 1,
                kind: 4,
                addend: -4,
            }],
        ),
    )
    .unwrap();
    let program = lim::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[object],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert!(inspect(&binary, &["-dW"]).contains("libc.so"));
    assert_runs(&binary, b"");
}

#[test]
fn supplied_static_object_links_bidirectionally_without_build_tools() {
    let scratch = support::Scratch::new("internal-static-object-link");
    let object = scratch.path().join("helper.o");
    fs::write(
        &object,
        fixture::object(
            &[fixture::Section {
                name: ".text",
                bytes: &[0xe8, 0, 0, 0, 0, 0xc3],
                size: 6,
                writable: false,
                executable: true,
            }],
            &[
                fixture::Symbol {
                    name: "helper",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "supplier",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[fixture::Relocation {
                section: 0,
                offset: 1,
                symbol: 1,
                kind: 4,
                addend: -4,
            }],
        ),
    )
    .unwrap();
    let input = scratch.path().join("main.lim");
    fs::write(
        &input,
        "(#extern-fn #abi-c helper () #u64)\n(#fn supplier () #u64 (#return 42u64))\n(#fn main () #u64 (#return (#unsafe (#unsafe-call helper (:)))))\n",
    )
    .unwrap();
    let binary = scratch.path().join("program");
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .arg("--link-object")
        .arg(&object)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_static(&binary);
    assert_runs(&binary, b"");
}

#[test]
fn supplied_object_data_and_bss_use_a_writable_segment() {
    let scratch = support::Scratch::new("internal-object-data-link");
    let object = scratch.path().join("data.o");
    let code = [
        0x48, 0xc7, 0x05, 0, 0, 0, 0, 1, 0, 0, 0, // movq $1, counter(%rip)
        0x48, 0x8b, 0x05, 0, 0, 0, 0, // mov shared_value(%rip), %rax
        0x48, 0x03, 0x05, 0, 0, 0, 0, // add counter(%rip), %rax
        0xc3,
    ];
    fs::write(
        &object,
        fixture::object(
            &[
                fixture::Section {
                    name: ".text",
                    bytes: &code,
                    size: code.len(),
                    writable: false,
                    executable: true,
                },
                fixture::Section {
                    name: ".data",
                    bytes: &42u64.to_le_bytes(),
                    size: 8,
                    writable: true,
                    executable: false,
                },
                fixture::Section {
                    name: ".bss",
                    bytes: &[],
                    size: 8,
                    writable: true,
                    executable: false,
                },
            ],
            &[
                fixture::Symbol {
                    name: "provided_value",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "shared_value",
                    section: Some(1),
                    value: 0,
                    global: false,
                },
                fixture::Symbol {
                    name: "counter",
                    section: Some(2),
                    value: 0,
                    global: false,
                },
            ],
            &[
                // The trailing imm32 means RIP is eight bytes after this rel32.
                fixture::Relocation {
                    section: 0,
                    offset: 3,
                    symbol: 2,
                    kind: 2,
                    addend: -8,
                },
                fixture::Relocation {
                    section: 0,
                    offset: 14,
                    symbol: 1,
                    kind: 2,
                    addend: -4,
                },
                fixture::Relocation {
                    section: 0,
                    offset: 21,
                    symbol: 2,
                    kind: 2,
                    addend: -4,
                },
            ],
        ),
    )
    .unwrap();
    let input = scratch.path().join("main.lim");
    fs::write(&input,
        "(#extern-fn #abi-c provided_value () #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call provided_value (:)))))\n"
    ).unwrap();
    let binary = scratch.path().join("program");
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .arg("--link-object")
        .arg(&object)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_static(&binary);
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(43));
    let segments = inspect(&binary, &["-lW"]);
    assert!(segments.contains("LOAD"));
    assert!(segments.contains("RW "), "{segments}");
}

#[test]
fn supplied_object_with_data_and_libc_import_links_without_tools() {
    let scratch = support::Scratch::new("internal-object-foreign-data-link");
    let object = scratch.path().join("helper.o");
    let code = [
        0x48, 0x83, 0xec, 0x08, // sub $8, %rsp
        0x8b, 0x3d, 0, 0, 0, 0, // mov value(%rip), %edi
        0xe8, 0, 0, 0, 0, // call abs
        0x48, 0x83, 0xc4, 0x08, 0xc3,
    ];
    fs::write(
        &object,
        fixture::object(
            &[
                fixture::Section {
                    name: ".text",
                    bytes: &code,
                    size: code.len(),
                    writable: false,
                    executable: true,
                },
                fixture::Section {
                    name: ".data",
                    bytes: &(-42i32).to_le_bytes(),
                    size: 4,
                    writable: true,
                    executable: false,
                },
            ],
            &[
                fixture::Symbol {
                    name: "provided_value",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "value",
                    section: Some(1),
                    value: 0,
                    global: false,
                },
                fixture::Symbol {
                    name: "abs",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[
                fixture::Relocation {
                    section: 0,
                    offset: 6,
                    symbol: 1,
                    kind: 2,
                    addend: -4,
                },
                fixture::Relocation {
                    section: 0,
                    offset: 11,
                    symbol: 2,
                    kind: 4,
                    addend: -4,
                },
            ],
        ),
    )
    .unwrap();
    let input = scratch.path().join("main.lim");
    fs::write(&input, "(#extern-fn #abi-c provided_value () #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call provided_value (:)))))\n").unwrap();
    let binary = scratch.path().join("program");
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .arg("--link-object")
        .arg(&object)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(inspect(&binary, &["-dW"]).contains("libc.so"));
    assert_runs(&binary, b"");
}

#[test]
fn pic_object_got_relocations_resolve_local_and_foreign_addresses() {
    let scratch = support::Scratch::new("internal-pic-object-link");
    let input = scratch.path().join("main.lim");
    fs::write(&input, "(#extern-fn #abi-c provided_value () #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call provided_value (:)))))\n").unwrap();
    for (name, code, symbol, expected_dynamic) in [
        (
            "local",
            vec![0x48, 0x8b, 0x05, 0, 0, 0, 0, 0x8b, 0x00, 0xc3],
            "value",
            false,
        ),
        (
            "foreign",
            vec![
                0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x05, 0, 0, 0, 0, 0xbf, 0xd6, 0xff, 0xff, 0xff,
                0xff, 0xd0, 0x48, 0x83, 0xc4, 0x08, 0xc3,
            ],
            "abs",
            true,
        ),
    ] {
        let object = scratch.path().join(format!("{name}.o"));
        let mut sections = vec![fixture::Section {
            name: ".text",
            bytes: &code,
            size: code.len(),
            writable: false,
            executable: true,
        }];
        let value = 42u32.to_le_bytes();
        if !expected_dynamic {
            sections.push(fixture::Section {
                name: ".data",
                bytes: &value,
                size: 4,
                writable: true,
                executable: false,
            });
        }
        fs::write(
            &object,
            fixture::object(
                &sections,
                &[
                    fixture::Symbol {
                        name: "provided_value",
                        section: Some(0),
                        value: 0,
                        global: true,
                    },
                    fixture::Symbol {
                        name: symbol,
                        section: if expected_dynamic { None } else { Some(1) },
                        value: 0,
                        global: expected_dynamic,
                    },
                ],
                &[fixture::Relocation {
                    section: 0,
                    offset: if expected_dynamic { 7 } else { 3 },
                    symbol: 1,
                    kind: 42,
                    addend: -4,
                }],
            ),
        )
        .unwrap();
        let binary = scratch.path().join(name);
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary)
            .arg("--link-object")
            .arg(&object)
            .env("PATH", scratch.path())
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        assert_eq!(
            Command::new(&binary).status().unwrap().code(),
            Some(42),
            "{name}"
        );
        assert_eq!(
            inspect(&binary, &["-lW"]).contains("INTERP"),
            expected_dynamic,
            "{name}"
        );
    }
}

#[test]
fn tls_data_pc32_is_rejected_instead_of_linking_to_a_call_stub() {
    let scratch = support::Scratch::new("external-data-pc32");
    let object = scratch.path().join("data.o");
    fs::write(
        &object,
        fixture::object(
            &[fixture::Section {
                name: ".text",
                bytes: &[0x48, 0x8b, 0x05, 0, 0, 0, 0, 0xc3],
                size: 8,
                writable: false,
                executable: true,
            }],
            &[
                fixture::Symbol {
                    name: "read_data",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "errno",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[fixture::Relocation {
                section: 0,
                offset: 3,
                symbol: 1,
                kind: 2,
                addend: -4,
            }],
        ),
    )
    .unwrap();
    let program = lim::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("program");
    let error = lim::link_native_binary(
        &assembly,
        &binary,
        &[object],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("no linked shared library has a sized data symbol"),
        "{error:?}"
    );
    assert!(!binary.exists());
}

#[test]
fn external_data_pc32_uses_an_internal_copy_relocation() {
    let scratch = support::Scratch::new("external-data-copy");
    let object = scratch.path().join("data.o");
    let code = [0x8b, 0x05, 0, 0, 0, 0, 0x83, 0xc0, 41, 0xc3];
    fs::write(
        &object,
        fixture::object(
            &[fixture::Section {
                name: ".text",
                bytes: &code,
                size: code.len(),
                writable: false,
                executable: true,
            }],
            &[
                fixture::Symbol {
                    name: "read_data",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "optind",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[fixture::Relocation {
                section: 0,
                offset: 2,
                symbol: 1,
                kind: 2,
                addend: -4,
            }],
        ),
    )
    .unwrap();
    let input = scratch.path().join("main.lim");
    fs::write(&input, "(#extern-fn #abi-c read_data () #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call read_data (:)))))\n").unwrap();
    let binary = scratch.path().join("program");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .arg("--link-object")
        .arg(&object)
        .env("PATH", scratch.path())
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
    assert!(inspect(&binary, &["-rDW"]).contains("R_X86_64_COPY"));
}

#[test]
fn writable_object_data_can_hold_a_shared_library_symbol_address() {
    let scratch = support::Scratch::new("foreign-absolute-data");
    let object = scratch.path().join("pointer.o");
    // Load the relocated pointer, then read glibc's optind (initially 1).
    let code = [
        0x48, 0x8b, 0x05, 0, 0, 0, 0, 0x8b, 0x00, 0x83, 0xc0, 41, 0xc3,
    ];
    fs::write(
        &object,
        fixture::object(
            &[
                fixture::Section {
                    name: ".text",
                    bytes: &code,
                    size: code.len(),
                    writable: false,
                    executable: true,
                },
                fixture::Section {
                    name: ".data",
                    bytes: &[0; 8],
                    size: 8,
                    writable: true,
                    executable: false,
                },
            ],
            &[
                fixture::Symbol {
                    name: "read_data",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "pointer",
                    section: Some(1),
                    value: 0,
                    global: false,
                },
                fixture::Symbol {
                    name: "optind",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[
                fixture::Relocation {
                    section: 0,
                    offset: 3,
                    symbol: 1,
                    kind: 2,
                    addend: -4,
                },
                fixture::Relocation {
                    section: 1,
                    offset: 0,
                    symbol: 2,
                    kind: 1,
                    addend: 0,
                },
            ],
        ),
    )
    .unwrap();
    let program = lim::parse_program("(#extern-fn #abi-c read_data () #u64) (#fn main () #u64 (#return (#unsafe (#unsafe-call read_data (:)))))").unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[object],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
    assert!(inspect(&binary, &["-rDW"]).contains("R_X86_64_64"));
}

#[test]
fn unresolved_weak_object_symbol_resolves_to_zero_without_a_library() {
    let scratch = support::Scratch::new("weak-absolute-data");
    let object = scratch.path().join("pointer.o");
    // Read the absolute pointer initialized from an undefined weak symbol.
    let code = [0x48, 0x8b, 0x05, 0, 0, 0, 0, 0x48, 0x83, 0xc0, 42, 0xc3];
    fs::write(
        &object,
        fixture::object_with_weak(
            &[
                fixture::Section {
                    name: ".text",
                    bytes: &code,
                    size: code.len(),
                    writable: false,
                    executable: true,
                },
                fixture::Section {
                    name: ".data",
                    bytes: &[0; 8],
                    size: 8,
                    writable: true,
                    executable: false,
                },
            ],
            &[
                fixture::Symbol {
                    name: "read_weak",
                    section: Some(0),
                    value: 0,
                    global: true,
                },
                fixture::Symbol {
                    name: "pointer",
                    section: Some(1),
                    value: 0,
                    global: false,
                },
                fixture::Symbol {
                    name: "optional_provider",
                    section: None,
                    value: 0,
                    global: true,
                },
            ],
            &[
                fixture::Relocation {
                    section: 0,
                    offset: 3,
                    symbol: 1,
                    kind: 2,
                    addend: -4,
                },
                fixture::Relocation {
                    section: 1,
                    offset: 0,
                    symbol: 2,
                    kind: 1,
                    addend: 0,
                },
            ],
            &[2],
        ),
    )
    .unwrap();
    let program = lim::parse_program("(#extern-fn #abi-c read_weak () #u64) (#fn main () #u64 (#return (#unsafe (#unsafe-call read_weak (:)))))").unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[object],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_static(&binary);
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
}

#[test]
fn pc_relative_foreign_data_relocations_work_from_writable_sections() {
    let scratch = support::Scratch::new("writable-foreign-relative");
    for (name, kind, code) in [
        (
            "copy",
            2,
            vec![
                0x48, 0x8d, 0x05, 0, 0, 0, 0, 0x48, 0x63, 0x08, 0x48, 0x01, 0xc8, 0x8b, 0x00, 0x83,
                0xc0, 41, 0xc3,
            ],
        ),
        (
            "got",
            9,
            vec![
                0x48, 0x8d, 0x05, 0, 0, 0, 0, 0x48, 0x63, 0x08, 0x48, 0x01, 0xc8, 0x48, 0x8b, 0x00,
                0x8b, 0x00, 0x83, 0xc0, 41, 0xc3,
            ],
        ),
    ] {
        let object = scratch.path().join(format!("{name}.o"));
        fs::write(
            &object,
            fixture::object(
                &[
                    fixture::Section {
                        name: ".text",
                        bytes: &code,
                        size: code.len(),
                        writable: false,
                        executable: true,
                    },
                    fixture::Section {
                        name: ".data",
                        bytes: &[0; 4],
                        size: 4,
                        writable: true,
                        executable: false,
                    },
                ],
                &[
                    fixture::Symbol {
                        name: "read_data",
                        section: Some(0),
                        value: 0,
                        global: true,
                    },
                    fixture::Symbol {
                        name: "relative",
                        section: Some(1),
                        value: 0,
                        global: false,
                    },
                    fixture::Symbol {
                        name: "optind",
                        section: None,
                        value: 0,
                        global: true,
                    },
                ],
                &[
                    fixture::Relocation {
                        section: 0,
                        offset: 3,
                        symbol: 1,
                        kind: 2,
                        addend: -4,
                    },
                    fixture::Relocation {
                        section: 1,
                        offset: 0,
                        symbol: 2,
                        kind,
                        addend: 0,
                    },
                ],
            ),
        )
        .unwrap();
        let program = lim::parse_program("(#extern-fn #abi-c read_data () #u64) (#fn main () #u64 (#return (#unsafe (#unsafe-call read_data (:)))))").unwrap();
        let assembly = lim::generate_assembly(&program).unwrap();
        let binary = scratch.path().join(name);
        lim::link_native_binary(
            &assembly,
            &binary,
            &[object],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        assert_eq!(
            Command::new(&binary).status().unwrap().code(),
            Some(42),
            "{name}"
        );
    }
}

#[test]
fn returning_from_main_exits_the_group_with_mains_status() {
    let scratch = support::Scratch::new("exit-group-entry");
    // Raw clone stays within one assembly block: the child has a fresh stack
    // and never returns through the parent's call frame. With SYS_exit in
    // _start, a later worker exit(0) can replace main's process status.
    let assembly = r#".intel_syntax noprefix
.text
.globl main
main:
    mov eax, 9
    xor edi, edi
    mov esi, 4096
    mov edx, 3
    mov r10d, 34
    mov r8, -1
    xor r9d, r9d
    syscall
    cmp rax, -4095
    jae failure
    lea rsi, [rax+4096]
    mov edi, 0x10f00
    xor edx, edx
    xor r10d, r10d
    xor r8d, r8d
    mov eax, 56
    syscall
    test rax, rax
    js failure
    jz worker
    mov eax, 42
    ret
worker:
    sub rsp, 16
    mov QWORD PTR [rsp], 0
    mov QWORD PTR [rsp+8], 50000000
    mov rdi, rsp
    xor esi, esi
    mov eax, 35
    syscall
    xor edi, edi
    mov eax, 60
    syscall
failure:
    ud2
.section .note.GNU-stack,"",@progbits
"#;
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_static(&binary);
    assert_runs(&binary, b"");
}
