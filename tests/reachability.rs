use std::{fs, path::Path, process::Command};

mod support;

fn assembly(source: &str, input: &Path, pruned: bool) -> Result<String, lim::Diagnostic> {
    let config = lim::CompileConfig::default();
    let directory = input.parent().unwrap().join(".lim");
    let cache = directory.join("cache");
    let compile = if pruned {
        lim::compile_executable_source_with_generated_sources
    } else {
        lim::compile_source_with_generated_sources
    };
    compile(
        source,
        input,
        &config,
        &cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
        None,
        &directory,
    )
}

#[test]
fn executable_keeps_transitive_callees_but_library_keeps_exports() {
    let scratch = support::Scratch::new("reachable-callees");
    let path = scratch.path().join("main.lim");
    let source = "(#fn unused () #u64 (#return 99u64))
        (#fn leaf ((x #u64)) #u64 (#return x))
        (#fn middle () #u64 (#return (#call leaf (: x 42u64))))
        (#fn main () #u64 (#return (#call middle (:))))";
    let full = assembly(source, &path, false).unwrap();
    let pruned = assembly(source, &path, true).unwrap();
    assert!(full.contains(".globl unused\n"));
    assert!(!pruned.contains(".globl unused\n"));
    for function in ["main", "middle", "leaf"] {
        assert!(pruned.contains(&format!(".globl {function}\n")));
    }
    assert!(pruned.len() < full.len());
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &pruned,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
}

#[test]
fn implicit_copy_clone_hooks_and_their_callees_are_retained() {
    let scratch = support::Scratch::new("reachable-clone-hooks");
    let source = "(#struct Value () ((number #u64)))
      (#type Alias Value)
      (#fn increment ((value Value)) Value
        (#return (#struct-literal Value
          (: number (#u64::add-wrap (#get value number) 1u64)))))
      (#fn Value::clone ((value Value)) Value
        (#return (#call increment (: value value))))
      (#fn unused () #u64 (#return 99u64))
      (#fn main () #u64
        (#let original Alias (#struct-literal Value (: number 41u64)))
        (#let copied Alias (#clone original))
        (#return (#get copied number)))";
    let pruned = assembly(source, &scratch.path().join("main.lim"), true).unwrap();
    assert!(pruned.contains(".globl Value_x2d_clone\n"), "{pruned}");
    assert!(pruned.contains(".globl increment\n"), "{pruned}");
    assert!(!pruned.contains(".globl unused\n"), "{pruned}");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &pruned,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        &mut Command::new(binary),
        std::time::Duration::from_secs(5),
        1024,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{status:?} {stderr:?}");
}

#[test]
fn implicit_clone_hooks_cannot_form_direct_or_mutual_recursion() {
    let sources = [
        "(#struct Value () ((number #u64)))
         (#fn Value::clone ((value Value)) Value (#return (#clone value)))",
        "(#struct Value () ((number #u64)))
         (#fn Value::clone ((value Value)) Value (#return (#call helper (: value value))))
         (#fn helper ((value Value)) Value (#return (#clone value)))",
        "(#struct Left () ((number #u64))) (#struct Right () ((number #u64)))
         (#fn Left::clone ((value Left)) Left
           (#let right Right (#clone (#struct-literal Right (: number 0u64))))
           (#return value))
         (#fn Right::clone ((value Right)) Right
           (#let left Left (#clone (#struct-literal Left (: number 0u64))))
           (#return value))",
    ];
    let scratch = support::Scratch::new("recursive-clone-hooks");
    for source in sources {
        let source = format!("{source} (#fn main () #u64 (#return 42u64))");
        for pruned in [false, true] {
            let error = assembly(&source, &scratch.path().join("main.lim"), pruned).unwrap_err();
            assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
            assert!(
                error.message.contains("recursive calls are not allowed"),
                "{error:?}"
            );
            let span = error.span.expect("recursion error has a source span");
            assert!(span.end > span.start, "{error:?}");
            assert_eq!(span.source_id, 0, "{error:?}");
        }
    }
}

#[test]
fn unused_imported_functions_are_still_checked() {
    let scratch = support::Scratch::new("reachable-validation");
    fs::write(
        scratch.path().join("unused.lim"),
        "(#fn unused () #u64 (#return false))",
    )
    .unwrap();
    let source = "(#import \"unused.lim\") (#fn main () #u64 (#return 42u64))";
    let error = assembly(source, &scratch.path().join("main.lim"), true).unwrap_err();
    let text = error.message.to_ascii_lowercase();
    assert!(text.contains("u64") && text.contains("bool"), "{text}");
}

#[test]
fn raw_assembly_symbol_calls_keep_their_callees() {
    let scratch = support::Scratch::new("reachable-asm");
    let source = "(#fn helper () #u64 (#return 42u64))
        (#fn unused () #u64 (#return 0u64))
        (#fn main () #u64 (#return (#unsafe (#asm #u64 () \"call helper\"))))";
    let pruned = assembly(source, &scratch.path().join("main.lim"), true).unwrap();
    assert!(pruned.contains(".globl helper\n"));
    assert!(!pruned.contains(".globl unused\n"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &pruned,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}

#[test]
fn thread_entry_workers_are_retained_without_direct_source_calls() {
    let scratch = support::Scratch::new("reachable-threads");
    let source = include_str!("../examples/thread_spawn.lim");
    let pruned = assembly(source, &scratch.path().join("main.lim"), true).unwrap();
    assert!(pruned.contains(".globl read_x2d_value\n"));
    assert!(!pruned.contains(".globl scale\n"));
    assert!(!pruned.contains(".Llim_thread_entry_ScaleTask:"));
    assert!(pruned.contains(".Llim_thread_entry_ReadValueTask:"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &pruned,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}

#[test]
fn cli_binary_prunes_but_emit_assembly_preserves_exports() {
    let scratch = support::Scratch::new("reachable-cli");
    let input = scratch.path().join("main.lim");
    fs::write(
        &input,
        "(#fn unused () #u64 (#return 99u64)) (#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
    let binary = scratch.path().join("program");
    let full_assembly = scratch.path().join("full.s");
    let full_binary = scratch.path().join("full");
    let compiler = env!("CARGO_BIN_EXE_lim");
    let output = Command::new(compiler)
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(compiler)
        .arg("--emit-asm")
        .arg(&input)
        .arg(&full_assembly)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let full = fs::read_to_string(full_assembly).unwrap();
    assert!(full.contains(".globl unused\n"));
    lim::link_native_binary(
        &full,
        &full_binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert!(fs::metadata(&binary).unwrap().len() < fs::metadata(full_binary).unwrap().len());
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}
