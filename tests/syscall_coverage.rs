//! Structural coverage only: execution and behavior belong to io_examples and
//! native_examples. Quoted forms/comments must not masquerade as runtime calls.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

mod support;

#[test]
fn raw_memory_wrappers_expose_caller_safety_obligations() {
    fn contains_pointer(ty: &lim::Type) -> bool {
        match ty {
            lim::Type::RawPointer { .. } => true,
            lim::Type::Reference { target, .. }
            | lim::Type::Slice(target)
            | lim::Type::MutableSlice(target)
            | lim::Type::Atomic(target)
            | lim::Type::Array(target, _) => contains_pointer(target),
            lim::Type::Tuple(fields) => fields.iter().any(contains_pointer),
            _ => false,
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = "(#import \"library/linux_x86_64.lim\")";
    // These APIs hide memory/process-state obligations in integer arguments
    // or in the operation itself, so pointer-type inspection is insufficient.
    let scalar_unsafe = [
        "linux-prctl",
        "linux-arch-prctl",
        "linux-ioctl",
        "linux-fcntl",
        "linux-semctl",
        "linux-brk",
        "linux-io-destroy",
        "linux-pkey-free",
        "linux-fork",
        "linux-exit",
        "linux-personality",
    ];
    let safe_helpers = [
        "linux-read-byte",
        "linux-write-byte",
        "linux-getrandom-byte",
        "linux-clock-gettime",
        "linux-nanosleep",
        "linux-getpid",
        "linux-exit-group",
    ];
    for os in ["linux", "unsupported"] {
        let mut config = lim::CompileConfig::default();
        config.set("os", os);
        config.set("arch", "x86_64");
        let program = lim::parse_program_from_path_with_config(
            source,
            &root.join("safety-check.lim"),
            &config,
        )
        .unwrap();
        let mut seen = BTreeSet::new();
        let mut unsafe_count = 0;
        for item in &program.items {
            let lim::Item::Function(function) = item else {
                continue;
            };
            seen.insert(function.name.as_str());
            if function.parameters.iter().any(|p| contains_pointer(&p.ty))
                || scalar_unsafe.contains(&function.name.as_str())
            {
                assert!(
                    function.unsafe_call,
                    "{os}: {} must require #unsafe",
                    function.name
                );
                unsafe_count += 1;
            }
            if safe_helpers.contains(&function.name.as_str()) {
                assert!(
                    !function.unsafe_call,
                    "{os}: {} should remain safe",
                    function.name
                );
            }
        }
        assert!(unsafe_count >= 201, "{os}: missing audited unsafe wrappers");
        for name in scalar_unsafe.iter().chain(&safe_helpers) {
            assert!(seen.contains(name), "{os}: missing wrapper {name}");
        }
    }
}

#[test]
fn unsupported_target_preserves_linux_wrapper_signatures() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = "(#import \"library/linux_x86_64.lim\")";
    let mut signatures = Vec::new();
    for os in ["linux", "unsupported"] {
        let mut config = lim::CompileConfig::default();
        config.set("os", os);
        config.set("arch", "x86_64");
        let program = lim::parse_program_from_path_with_config(
            source,
            &root.join("signature-check.lim"),
            &config,
        )
        .unwrap();
        lim::check_types(&program).unwrap();
        let functions: BTreeMap<_, _> = program
            .items
            .into_iter()
            .filter_map(|item| {
                let lim::Item::Function(function) = item else {
                    return None;
                };
                Some((
                    function.name,
                    (
                        function.parameters,
                        function.return_type,
                        function.unsafe_call,
                    ),
                ))
            })
            .collect();
        signatures.push(functions);
    }
    assert_eq!(
        signatures[0], signatures[1],
        "cfg fallbacks changed public signatures"
    );
}

#[test]
fn linux_library_emits_without_external_declarations() {
    let scratch = support::Scratch::new("syscall-library-emission");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = "(#import \"library/linux_x86_64.lim\")\n(#fn main () u64 (#return 0u64))";
    let mut config = lim::CompileConfig::default();
    config.set("os", "linux");
    config.set("arch", "x86_64");
    let assembly = lim::compile_source_to_assembly(
        source,
        &root.join("library-emission-check.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("library emission: {}", error.message));
    assert!(assembly.lines().any(|line| line.trim() == "syscall"));
    for line in assembly.lines() {
        assert!(
            !line.trim_start().starts_with(".extern "),
            "external dependency: {line}"
        );
    }
}

fn walk(expression: &lim::Expr, visit: &mut impl FnMut(&lim::Expr)) {
    visit(expression);
    if let lim::Expr::List(items) = expression {
        for item in items {
            walk(item, visit);
        }
    }
}

fn symbol(expression: Option<&lim::Expr>) -> Option<&str> {
    match expression {
        Some(lim::Expr::Symbol(name)) => Some(name),
        _ => None,
    }
}

fn calls(source: &str) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    for form in lim::parse(source).unwrap() {
        walk(&form.expr, &mut |expression| {
            if let lim::Expr::List(items) = expression {
                if symbol(items.first()) == Some("#call") {
                    if let Some(name) = symbol(items.get(1)) {
                        result.insert(name.to_owned());
                    }
                }
            }
        });
    }
    result
}

#[test]
fn linux_wrappers_have_runnable_call_sites_and_catalogued_syscalls() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut call_sites: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let manifest = include_str!("../examples/outcomes.txt");
    let mut sources = Vec::new();
    for line in manifest.lines().filter(|line| !line.starts_with('#')) {
        let fields: Vec<_> = line.split_whitespace().collect();
        if fields
            .first()
            .is_some_and(|kind| matches!(*kind, "exit" | "signal"))
        {
            sources.push(format!("examples/{}", fields[2]));
        }
    }
    // These two programs need a paired build/run harness rather than the
    // standalone examples runner. Keep this explicit to avoid counting UI
    // failures or arbitrary unused fixture files as runnable coverage.
    sources.extend([
        "tests/fixtures/exec_driver.lim".into(),
        "tests/fixtures/exec_target.lim".into(),
        // The echo harness supplies stdin; the generic runner treats it as a module.
        "examples/echo_input.lim".into(),
        // These operation wrappers are exercised through their imported Lim example.
        "library/async_stdin_byte.lim".into(),
    ]);
    for path in sources {
        for name in calls(&fs::read_to_string(root.join(&path)).unwrap()) {
            call_sites.entry(name).or_default().insert(path.clone());
        }
    }

    let catalog: BTreeSet<_> =
        lim::parse(include_str!("../library/linux_x86_64_syscall_numbers.lim"))
            .unwrap()
            .into_iter()
            .map(|form| {
                let lim::Expr::List(items) = form.expr else {
                    panic!("catalog declaration");
                };
                symbol(items.get(1)).unwrap().to_owned()
            })
            .collect();
    let mut implementations: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut wrappers = BTreeSet::new();
    for form in lim::parse(include_str!("../library/linux_x86_64.lim")).unwrap() {
        walk(&form.expr, &mut |expression| {
            let lim::Expr::List(items) = expression else {
                return;
            };
            if !matches!(symbol(items.first()), Some("#fn" | "#unsafe-fn")) {
                return;
            }
            let name = symbol(items.get(1)).unwrap();
            if !name.starts_with("linux-") {
                return;
            }
            wrappers.insert(name.to_owned());
            walk(expression, &mut |nested| {
                if let lim::Expr::Symbol(syscall) = nested {
                    if syscall.starts_with("LINUX-SYS-") {
                        assert!(catalog.contains(syscall), "{name}: unknown {syscall}");
                        implementations
                            .entry(syscall.clone())
                            .or_default()
                            .insert(name.to_owned());
                    }
                }
            });
        });
    }
    for wrapper in &wrappers {
        assert!(
            call_sites.contains_key(wrapper),
            "{wrapper} has no runnable test call site"
        );
    }
    // Prevent accidental coverage loss, without claiming that this floor
    // proves successful execution of every path through these syscalls.
    assert!(
        implementations.len() >= 278,
        "syscall implementation coverage regressed"
    );
    println!(
        "{} / {} catalog syscalls referenced; {} wrappers have runnable call sites",
        implementations.len(),
        catalog.len(),
        wrappers.len()
    );
    for (syscall, functions) in &implementations {
        for function in functions {
            println!(
                "{syscall}\t{function}\t{}",
                call_sites[function]
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }
    for missing in catalog
        .iter()
        .filter(|name| !implementations.contains_key(*name))
    {
        println!("MISSING\t{missing}");
    }
}

#[test]
fn library_sources_only_declare_the_standard_allocator_ffi() {
    // Core OS services remain syscall-only. The explicitly system-allocated
    // String library adds exactly these three process allocator declarations,
    // not a general exemption for FFI elsewhere or in generated templates.
    let allocator = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/system_allocator.lim");
    let expected: BTreeMap<_, _> = lim::parse(
        "(#extern-fn #abi-c malloc (: size usize) (#ptr-mut u8))
         (#extern-fn #abi-c realloc (: pointer (#ptr-mut u8) : size usize) (#ptr-mut u8))
         (#extern-fn #abi-c free (: pointer (#ptr-mut u8)) ())",
    )
    .unwrap()
    .into_iter()
    .map(|form| {
        let lim::Expr::List(items) = &form.expr else {
            unreachable!()
        };
        let name = symbol(items.get(2)).unwrap().to_owned();
        (name, form.expr)
    })
    .collect();
    fn inspect(
        path: &Path,
        allocator: &Path,
        expected: &BTreeMap<String, lim::Expr>,
        seen: &mut BTreeSet<String>,
    ) {
        for entry in fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                inspect(&path, allocator, expected, seen);
            } else if path.extension().is_some_and(|ext| ext == "lim") {
                // Spanned children also traverse quote/templates, ensuring
                // generators cannot hide an external declaration in output.
                fn visit(
                    form: &lim::SpannedExpr,
                    path: &Path,
                    allocator: &Path,
                    expected: &BTreeMap<String, lim::Expr>,
                    seen: &mut BTreeSet<String>,
                    top_level: bool,
                ) {
                    if let lim::Expr::List(items) = &form.expr {
                        if symbol(items.first()) == Some("#extern-fn") {
                            assert!(
                                path == allocator && top_level,
                                "unexpected FFI in {}",
                                path.display()
                            );
                            let name = symbol(items.get(2)).expect("C allocator function name");
                            assert_eq!(
                                Some(&form.expr),
                                expected.get(name),
                                "unexpected allocator ABI: {name}"
                            );
                            assert!(
                                seen.insert(name.to_owned()),
                                "duplicate allocator declaration: {name}"
                            );
                        }
                    }
                    for child in &form.children {
                        visit(child, path, allocator, expected, seen, false);
                    }
                }
                for form in lim::parse(&fs::read_to_string(&path).unwrap()).unwrap() {
                    visit(&form, &path, allocator, expected, seen, true);
                }
            }
        }
    }
    let mut seen = BTreeSet::new();
    inspect(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("library"),
        &allocator,
        &expected,
        &mut seen,
    );
    assert_eq!(seen, expected.into_keys().collect());
}

#[test]
fn comments_strings_and_quoted_calls_are_not_runtime_evidence() {
    let found = calls("; (#call comment (:))\n\"(#call string (:))\"\n'(#call quoted (:))\n(#fn f () () (#call real (:)) (#return ()))");
    assert_eq!(found, BTreeSet::from(["real".to_owned()]));
}
