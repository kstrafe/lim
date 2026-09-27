use std::{
    collections::HashSet,
    env, fs,
    hint::black_box,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

fn measure(label: &str, iterations: usize, mut operation: impl FnMut()) -> Duration {
    let start = Instant::now();
    for _ in 0..iterations {
        operation();
    }
    let elapsed = start.elapsed();
    println!(
        "{label}: iterations={iterations} total_ms={:.3} ns_per_iteration={:.0}",
        elapsed.as_secs_f64() * 1000.0,
        elapsed.as_nanos() as f64 / iterations as f64
    );
    elapsed
}

fn report_symbol_repetition(label: &str, source: &str) {
    let tokens = lim::lex(source).expect("benchmark source lexes");
    let symbols = tokens.iter().filter_map(|token| match &token.kind {
        lim::TokenKind::Symbol(value) => Some(value.as_str()),
        _ => None,
    });
    let mut unique = HashSet::new();
    let mut occurrences = 0usize;
    let mut repeated_bytes = 0usize;
    for symbol in symbols {
        occurrences += 1;
        if !unique.insert(symbol) {
            repeated_bytes += symbol.len();
        }
    }
    println!(
        "{label}.symbols occurrences={occurrences} unique={} repeated_text_bytes={repeated_bytes}",
        unique.len()
    );
}

fn temp_root() -> PathBuf {
    let path = env::temp_dir().join(format!("lim-perf-{}", std::process::id()));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).unwrap();
    path
}

fn generated_program(functions: usize) -> String {
    let mut source = String::new();
    for index in 0..functions {
        source.push_str(&format!("(#fn work-{index} () u64 (#return {index}u64))\n"));
    }
    source.push_str("(#fn main () u64 (#return 42u64))\n");
    source
}

fn generator_program(aliases: usize) -> String {
    let mut source = String::from(
        "(#gn aliases (pairs) (#gn-for-each pair pairs (#gn-list (#gn-symbol \"#type\") (#gn-first pair) (#gn-first (#gn-rest pair)))))\n(@aliases (",
    );
    for index in 0..aliases {
        source.push_str(&format!("(Generated{index} u64) "));
    }
    source.push_str("))\n(#fn main () u64 (#return 42u64))\n");
    source
}

fn compile_and_link(source: &str, source_path: &Path, directory: &Path) -> (String, PathBuf) {
    fs::create_dir_all(directory).unwrap();
    let config = lim::CompileConfig::default();
    let generated = directory.join(".lim");
    let cache = generated.join("cache");
    fs::create_dir_all(&generated).unwrap();
    fs::create_dir_all(&cache).unwrap();
    lim::write_generated_sources_diagnostic(source, source_path, &generated, &config, &cache)
        .unwrap_or_else(|error| panic!("generator phase failed: {}", error.message));
    let assembly = lim::compile_source_to_assembly(
        source,
        source_path,
        &config,
        &cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("compile phase failed: {}", error.message));
    let assembly_path = directory.join("program.s");
    fs::write(&assembly_path, &assembly).unwrap();
    let binary = directory.join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("production link failed: {}", error.message));
    (assembly, binary)
}

fn main() {
    let iterations = env::args()
        .skip(1)
        .collect::<Vec<_>>()
        .windows(2)
        .find(|args| args[0] == "--iterations")
        .and_then(|args| args[1].parse::<usize>().ok())
        .unwrap_or(20)
        .max(1);
    let root = temp_root();
    let small = generated_program(4);
    let large = generated_program(256);
    println!(
        "lim={} target=x86_64-sysv arch={} os={} rustc={} backend=internal-x86_64-elf machine={}",
        env!("CARGO_PKG_VERSION"),
        env::consts::ARCH,
        env::consts::OS,
        Command::new("rustc")
            .arg("--version")
            .output()
            .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
            .unwrap_or_else(|_| "unavailable".into()),
        Command::new("uname")
            .arg("-srmo")
            .output()
            .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
            .unwrap_or_else(|_| "unavailable".into()),
    );
    if let Ok(cpuinfo) = fs::read_to_string("/proc/cpuinfo") {
        if let Some(model) = cpuinfo.lines().find_map(|line| {
            line.strip_prefix("model name\t: ")
                .or_else(|| line.strip_prefix("Hardware\t: "))
        }) {
            println!("cpu_model: {model}");
        }
    }
    println!(
        "small_source_bytes={} large_source_bytes={}",
        small.len(),
        large.len()
    );

    let shared_path = root.join("shared.lim");
    fs::write(&shared_path, "(#type SharedMarker u64)\n").unwrap();
    for (label, source) in [("small", &small), ("large", &large)] {
        report_symbol_repetition(label, source);
        measure(&format!("{label}.lex"), iterations, || {
            black_box(lim::lex(black_box(source)).unwrap());
        });
        measure(&format!("{label}.parse"), iterations, || {
            black_box(lim::parse(black_box(source)).unwrap());
        });
        let project_source = format!(
            "(#import \"shared.lim\")\n(#cfg-if (#cfg-is #platform linux) (#fn cfg-enabled () u64 (#return 1u64)))\n{source}"
        );
        let path = root.join(format!("{label}.lim"));
        fs::write(&path, &project_source).unwrap();
        let mut project_config = lim::CompileConfig::default();
        project_config.set("platform", "linux");
        let frontend_cache = root.join("frontend-cache");
        measure(&format!("{label}.imports-cfg-frontend"), iterations, || {
            black_box(
                lim::parse_program_from_path_with_config_and_cache(
                    &project_source,
                    &path,
                    &project_config,
                    &frontend_cache,
                )
                .unwrap(),
            );
        });
        let program = lim::parse_program_from_path_with_config_and_cache(
            &project_source,
            &path,
            &project_config,
            &frontend_cache,
        )
        .unwrap();
        measure(&format!("{label}.semantic"), iterations, || {
            lim::check_types(black_box(&program)).unwrap();
        });
        let checked = lim::CheckedProgram::validate(&program).unwrap();
        measure(
            &format!("{label}.checked-native-emission"),
            iterations,
            || {
                black_box(
                    checked
                        .generate_assembly(lim::TargetDescription::X86_64_SYSTEM_V)
                        .unwrap(),
                );
            },
        );
        measure(&format!("{label}.compile-end-to-end"), iterations, || {
            black_box(
                lim::compile_source_to_assembly(
                    &project_source,
                    &path,
                    &project_config,
                    &frontend_cache,
                    lim::TargetDescription::X86_64_SYSTEM_V,
                )
                .unwrap(),
            );
        });
        let assembly = lim::generate_assembly(&program).unwrap();
        let assembly_path = root.join(format!("{label}-link.s"));
        let binary_path = root.join(format!("{label}-link"));
        fs::write(&assembly_path, &assembly).unwrap();
        measure(&format!("{label}.link"), iterations, || {
            lim::link_native_binary(
                &assembly,
                &binary_path,
                &[],
                &[],
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
        });
        assert_eq!(
            Command::new(&binary_path).status().unwrap().code(),
            Some(42)
        );
        println!(
            "{label}.artifacts assembly_bytes={} binary_bytes={}",
            fs::metadata(&assembly_path).unwrap().len(),
            fs::metadata(&binary_path).unwrap().len()
        );
    }

    let config = lim::CompileConfig::default();
    for (label, aliases) in [("small", 4), ("large", 256)] {
        let generator_source = generator_program(aliases);
        report_symbol_repetition(&format!("{label}.generator"), &generator_source);
        let generator_path = root.join(format!("generator-{label}.lim"));
        fs::write(&generator_path, &generator_source).unwrap();
        let generated_dir = root.join(format!("generator-output-{label}"));
        let cache_dir = root.join(format!("generator-cache-{label}"));
        fs::create_dir_all(&generated_dir).unwrap();
        fs::create_dir_all(&cache_dir).unwrap();
        measure(&format!("{label}.generator-cold-cache"), iterations, || {
            let _ = fs::remove_dir_all(&cache_dir);
            fs::create_dir_all(&cache_dir).unwrap();
            lim::write_generated_sources_from_path_with_config_and_cache(
                &generator_source,
                &generator_path,
                &generated_dir,
                &config,
                &cache_dir,
            )
            .unwrap();
        });
        lim::write_generated_sources_from_path_with_config_and_cache(
            &generator_source,
            &generator_path,
            &generated_dir,
            &config,
            &cache_dir,
        )
        .unwrap();
        measure(&format!("{label}.generator-warm-cache"), iterations, || {
            lim::write_generated_sources_from_path_with_config_and_cache(
                &generator_source,
                &generator_path,
                &generated_dir,
                &config,
                &cache_dir,
            )
            .unwrap();
        });
    }
    if let Ok(status) = fs::read_to_string("/proc/self/status") {
        if let Some(peak) = status.lines().find(|line| line.starts_with("VmHWM:")) {
            println!("process_peak_memory: {peak}");
        }
    }

    let mut chain = String::from("(#fn step-0 () u64 (#return 42u64))\n");
    for index in 1..64 {
        chain.push_str(&format!(
            "(#fn step-{index} () u64 (#return (#if true (#call step-{} (:)) 0u64)))\n",
            index - 1
        ));
    }
    chain.push_str("(#fn main () u64 (#return (#call step-63 (:))))");
    let generated = generator_program(256);
    for (name, source, expected) in [
        (
            "large_reference_projections",
            include_str!("../examples/large_reference_projections.lim"),
            42,
        ),
        (
            "vec_allocator",
            include_str!("../examples/vec_allocator.lim"),
            4,
        ),
        ("branch_call_chain", chain.as_str(), 42),
        ("generator_heavy", generated.as_str(), 42),
    ] {
        report_symbol_repetition(name, source);
        let directory = root.join(name);
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("workload.lim");
        fs::write(&path, source).unwrap();
        let source_path = if name == "vec_allocator" {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/vec_allocator.lim")
        } else {
            path
        };
        for temperature in ["cold", "warm"] {
            measure(&format!("{name}.build-{temperature}"), iterations, || {
                if temperature == "cold" {
                    let cache = directory.join(".lim/cache");
                    if cache.exists() {
                        fs::remove_dir_all(cache).unwrap();
                    }
                }
                let (_, binary) = compile_and_link(source, &source_path, &directory);
                assert_eq!(
                    Command::new(binary).status().unwrap().code(),
                    Some(expected)
                );
            });
        }
        let binary = directory.join("program");
        let start = Instant::now();
        let status = Command::new(&binary).status().expect("run native workload");
        let elapsed = start.elapsed();
        assert_eq!(status.code(), Some(expected));
        println!(
            "runtime.{name}: elapsed_ns={} checked_exit={expected} assembly_bytes={} binary_bytes={}",
            elapsed.as_nanos(),
            fs::metadata(directory.join("program.s")).unwrap().len(),
            fs::metadata(&binary).unwrap().len()
        );
    }
    let _ = fs::remove_dir_all(root);
}
