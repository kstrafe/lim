use std::{fs, path::Path, process::Command, time::Duration};

mod support;

const DECLARATION: &str = "(#unsafe-fn answer () u64 (#return 42u64))\n";

fn compile(source: &str, path: &Path, cache: &Path) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        path,
        &lim::CompileConfig::default(),
        cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn unsafe_calls_require_a_block_and_highlight_the_callee() {
    let scratch = support::Scratch::new("unsafe-function");
    let source = format!("{DECLARATION}(#fn main () u64 (#return (#call answer (:))))");
    let error = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), "E4300");
    assert!(error.message.contains("call to unsafe function 'answer'"));
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "answer");
    let source = format!("{DECLARATION}(#fn main () u64 (#return (#unsafe (#call answer (:)))))");
    let assembly = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
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
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(42));
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn declaration_does_not_make_the_function_body_implicitly_unsafe() {
    let scratch = support::Scratch::new("unsafe-body");
    let source = "(#unsafe-fn read-byte ((pointer (#ptr u8))) u8 (#return (#ptr-read pointer)))";
    let error = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), "E4300");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#ptr-read");
}

#[test]
fn external_imports_and_generated_declarations_preserve_safety() {
    let scratch = support::Scratch::new("unsafe-import-generator");
    fs::write(scratch.path().join("module.lim"), DECLARATION).unwrap();
    for source in [
        "(#import-external \"module.lim\" ext-) (#fn main () u64 (#return (#call ext-answer (:))))",
        "(#gn make (name) `((#unsafe-fn ,name () u64 (#return 42u64)))) (@make answer) (#fn main () u64 (#return (#call answer (:))))",
    ] {
        let error = compile(source, &scratch.path().join("main.lim"), &scratch.path().join("cache")).unwrap_err();
        assert_eq!(error.code_string(), "E4300", "{}", error.message);
        assert!(error.message.contains("call to unsafe function"));
    }
}

#[test]
fn implicit_entry_points_cannot_bypass_unsafe_calls() {
    let scratch = support::Scratch::new("unsafe-implicit-call");
    for (source, message) in [
        ("(#unsafe-fn main () u64 (#return 42u64))", "implicit entry point 'main' must be safe"),
        ("(#struct Value ((n u64))) (#unsafe-fn Value-clone ((value Value)) Value (#return value))", "implicit entry point 'Value-clone' must be safe"),
        ("(#unsafe-fn worker () u64 (#return 42u64)) (@thread-spawn (: task Task : worker worker))", "thread worker 'worker' must be safe"),
    ] {
        let error = compile(source, &scratch.path().join("main.lim"), &scratch.path().join("cache")).unwrap_err();
        assert!(error.message.contains(message), "{}", error.message);
        assert!(error.span.is_some());
    }
}

#[test]
fn io_uring_raw_pointer_contracts_are_enforced() {
    let scratch = support::Scratch::new("unsafe-syscall");
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/linux_x86_64.lim");
    let source = format!("(#import {:?}) (#fn main () i64 (#return (#call linux-io-uring-setup (: entries 2u32 : parameters (#ptr-null (#ptr-mut u8))))))", library.to_str().unwrap());
    let error = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), "E4300");
    assert!(error.message.contains("linux-io-uring-setup"));
}

#[test]
fn every_unsafe_linux_wrapper_rejects_safe_calls_in_both_cfg_branches() {
    use std::collections::BTreeMap;

    fn collect(
        node: &lim::SpannedExpr,
        source: &str,
        probes: &mut BTreeMap<String, (String, String)>,
    ) {
        if !matches!(node.expr, lim::Expr::List(_)) {
            return;
        }
        let items = &node.children;
        if matches!(items.first().map(|n| &n.expr), Some(lim::Expr::Symbol(head)) if head == "#unsafe-fn")
        {
            let lim::Expr::Symbol(name) = &items[1].expr else {
                panic!("function name")
            };
            let parameters = &source[items[2].span.start..items[2].span.end];
            let result = &source[items[3].span.start..items[3].span.end];
            let mut arguments = String::new();
            for parameter in &items[2].children {
                let lim::Expr::Symbol(name) = &parameter.children[0].expr else {
                    panic!("parameter name")
                };
                arguments.push_str(&format!(" ({name} {name})"));
            }
            let signature = format!("(#fn probe-{name} {parameters} {result}");
            let call = format!("(#call {name} ({arguments}))");
            // The structural coverage suite compares signatures. Here retain
            // one spelling: cfg branches may format the same types differently.
            probes.entry(name.clone()).or_insert((signature, call));
        }
        for child in items {
            collect(child, source, probes);
        }
    }

    let scratch = support::Scratch::new("unsafe-all-syscalls");
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/linux_x86_64.lim");
    let contents = fs::read_to_string(&library).unwrap();
    let mut probes = BTreeMap::new();
    for node in lim::parse(&contents).unwrap() {
        collect(&node, &contents, &mut probes);
    }
    assert!(probes.len() >= 201);
    let import = format!("(#import {:?})\n", library.to_str().unwrap());
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    for os in ["linux", "unsupported"] {
        let mut config = lim::CompileConfig::default();
        config.set("os", os);
        config.set("arch", "x86_64");
        let mut explicit = import.clone();
        for (name, (signature, call)) in &probes {
            let source = format!("{import}{signature} (#return {call}))");
            let error = lim::compile_source_to_assembly(
                &source,
                &path,
                &config,
                &cache,
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_err();
            assert_eq!(
                error.code_string(),
                "E4300",
                "{os}: {name}: {}",
                error.message
            );
            assert!(
                error
                    .message
                    .contains(&format!("call to unsafe function '{name}'")),
                "{}",
                error.message
            );
            let span = error.span.unwrap();
            assert_eq!(
                &source[span.start..span.end],
                name,
                "{os}: diagnostic location"
            );
            explicit.push_str(&format!("{signature} (#return (#unsafe {call})))\n"));
        }
        // Compile but do not execute: these forwarders intentionally have no
        // resources or valid buffers of their own. Runtime behavior is tested
        // by the syscall examples with real allocation/lifetime management.
        lim::compile_source_to_assembly(
            &explicit,
            &path,
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{os}: explicit unsafe calls: {}", error.message));
    }
}

#[test]
fn safe_generator_capabilities_reject_unsafe_operations() {
    let scratch = support::Scratch::new("unsafe-capability");
    let source = "(#unsafe-fn less ((a (#ref u64)) (b (#ref u64))) bool (#return false))
      (#capability ordered u64 ((less ((#ref u64) (#ref u64)) bool)))";
    let error = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert!(
        error.message.contains("contract requires"),
        "{}",
        error.message
    );
    assert!(error.message.contains("unsafe"));
}
