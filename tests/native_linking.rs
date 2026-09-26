//! Verify the published ELF, not just the absence of source FFI declarations.
use std::{fs, path::Path, process::Command, time::Duration};

mod support;

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
fn syscall_library_binary_has_no_interpreter_or_dynamic_dependencies() {
    let scratch = support::Scratch::new("syscall-static-link");
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/linux_x86_64.lim");
    let source = format!(
        "(#import {:?}) (#fn main () u64
          (#let letter u8 83u8)
          (#assert (#i64.== (#call linux-write-byte (#fn-args (source (#borrow letter)))) 1i64))
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
        "(#extern-fn #abi-c abs ((value i32)) i32)
         (#fn main () u64 (#return 42u64))",
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
        "(#fn main () u64 (#return 42u64))",
        scratch.path(),
        &["m".into()],
    );
    assert_runs(&binary, b"");
    // Nix may supply --as-needed: executing successfully establishes that the
    // requested library was found. Missing explicit libraries must still fail.
    let original = fs::read(&binary).unwrap();
    let program = lim::parse_program("(#fn main () u64 (#return 42u64))").unwrap();
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
    let source = scratch.path().join("helper.s");
    let object = scratch.path().join("helper.o");
    fs::write(
        &source,
        ".text\n.globl helper\nhelper:\n jmp abs\n.section .note.GNU-stack,\"\",@progbits\n",
    )
    .unwrap();
    assert!(Command::new("as")
        .arg("--64")
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .status()
        .unwrap()
        .success());
    let program = lim::parse_program("(#fn main () u64 (#return 42u64))").unwrap();
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
