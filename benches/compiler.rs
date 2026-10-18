use std::{
    alloc::{GlobalAlloc, Layout, System},
    collections::{HashMap, HashSet},
    env, fs,
    hint::black_box,
    path::{Path, PathBuf},
    process::Command,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

struct CountingAllocator;

static ALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);
static ALLOC_BYTES: AtomicUsize = AtomicUsize::new(0);
static DEALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);
static DEALLOC_BYTES: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = System.alloc(layout);
        if !pointer.is_null() {
            ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            ALLOC_BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        DEALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        DEALLOC_BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        System.dealloc(pointer, layout);
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_pointer = System.realloc(pointer, layout, new_size);
        if !new_pointer.is_null() {
            ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            ALLOC_BYTES.fetch_add(new_size, Ordering::Relaxed);
            DEALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            DEALLOC_BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        }
        new_pointer
    }
}

#[global_allocator]
static GLOBAL: CountingAllocator = CountingAllocator;

#[derive(Clone, Copy)]
struct AllocationCounts {
    calls: usize,
    bytes: usize,
    dealloc_calls: usize,
    dealloc_bytes: usize,
}

fn allocation_counts() -> AllocationCounts {
    AllocationCounts {
        calls: ALLOC_CALLS.load(Ordering::Relaxed),
        bytes: ALLOC_BYTES.load(Ordering::Relaxed),
        dealloc_calls: DEALLOC_CALLS.load(Ordering::Relaxed),
        dealloc_bytes: DEALLOC_BYTES.load(Ordering::Relaxed),
    }
}

fn report_allocations(label: &str, iterations: usize, mut operation: impl FnMut()) {
    let before = allocation_counts();
    for _ in 0..iterations {
        operation();
    }
    let after = allocation_counts();
    println!(
        "{label}: iterations={iterations} alloc_calls_per_iteration={:.1} requested_bytes_per_iteration={:.0} dealloc_calls_per_iteration={:.1} deallocated_bytes_per_iteration={:.0}",
        (after.calls - before.calls) as f64 / iterations as f64,
        (after.bytes - before.bytes) as f64 / iterations as f64,
        (after.dealloc_calls - before.dealloc_calls) as f64 / iterations as f64,
        (after.dealloc_bytes - before.dealloc_bytes) as f64 / iterations as f64,
    );
}

fn report_mirror_allocations(label: &str, source: &str, iterations: usize) {
    let mut calls = 0usize;
    let mut bytes = 0usize;
    for _ in 0..iterations {
        let ast = lim::parse(black_box(source)).unwrap();
        let before = allocation_counts();
        let mut symbols = LocalSymbols::default();
        let interned = ast
            .iter()
            .map(|node| intern_node(node, &mut symbols))
            .collect::<Vec<_>>();
        let after = allocation_counts();
        calls += after.calls - before.calls;
        bytes += after.bytes - before.bytes;
        black_box((&interned, &symbols.by_text));
    }
    println!(
        "{label}: iterations={iterations} alloc_calls_per_iteration={:.1} requested_bytes_per_iteration={:.0} (mirror construction only; parsed input already exists)",
        calls as f64 / iterations as f64,
        bytes as f64 / iterations as f64,
    );
}

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

fn clone_symbol_text(tokens: &[lim::Token]) -> Vec<String> {
    tokens
        .iter()
        .filter_map(|token| match &token.kind {
            lim::TokenKind::Symbol(value) => Some(value.clone()),
            _ => None,
        })
        .collect()
}

fn intern_symbol_text(tokens: &[lim::Token]) -> (Vec<Arc<str>>, Vec<u32>) {
    let mut symbols = Vec::new();
    let mut ids = Vec::new();
    let mut lookup = HashMap::new();
    for token in tokens {
        let lim::TokenKind::Symbol(value) = &token.kind else {
            continue;
        };
        let id = if let Some(id) = lookup.get(value.as_str()) {
            *id
        } else {
            let id = u32::try_from(symbols.len()).expect("benchmark symbol count fits #u32");
            let symbol = Arc::<str>::from(value.as_str());
            lookup.insert(symbol.clone(), id);
            symbols.push(symbol);
            id
        };
        ids.push(id);
    }
    (symbols, ids)
}

// A benchmark-only mirror of the parsed syntax tree. In the hot path every
// symbol node carries an ID and its one spelling is owned by this compilation's
// pool; source spans and child shape are retained just like SpannedExpr.
#[derive(Debug)]
#[allow(dead_code)] // Fields are intentionally retained as the benchmark AST payload.
enum InternedKind {
    List(Vec<InternedKind>),
    Symbol(u32),
    Unary(Box<InternedKind>),
    Other(lim::Expr),
}

#[derive(Debug)]
#[allow(dead_code)] // Keep the source AST's span and child structure in the A/B value.
struct InternedNode {
    kind: InternedKind,
    span: lim::Span,
    children: Vec<InternedNode>,
}

#[derive(Default)]
struct LocalSymbols {
    by_text: HashMap<String, u32>,
}

impl LocalSymbols {
    fn id(&mut self, text: &str) -> u32 {
        if let Some(id) = self.by_text.get(text) {
            return *id;
        }
        let id = u32::try_from(self.by_text.len()).expect("benchmark symbol count fits #u32");
        self.by_text.insert(text.to_owned(), id);
        id
    }
}

fn intern_node(node: &lim::SpannedExpr, symbols: &mut LocalSymbols) -> InternedNode {
    let kind = match &node.expr {
        lim::Expr::Symbol(text) => InternedKind::Symbol(symbols.id(text)),
        lim::Expr::List(items) => InternedKind::List(
            items
                .iter()
                .map(|item| intern_expr(item, symbols))
                .collect(),
        ),
        lim::Expr::Quote(value)
        | lim::Expr::QuasiQuote(value)
        | lim::Expr::Unquote(value)
        | lim::Expr::UnquoteSplicing(value) => {
            InternedKind::Unary(Box::new(intern_expr(value, symbols)))
        }
        other => InternedKind::Other(other.clone()),
    };
    InternedNode {
        kind,
        span: node.span,
        children: node
            .children
            .iter()
            .map(|child| intern_node(child, symbols))
            .collect(),
    }
}

fn intern_expr(expression: &lim::Expr, symbols: &mut LocalSymbols) -> InternedKind {
    match expression {
        lim::Expr::Symbol(text) => InternedKind::Symbol(symbols.id(text)),
        lim::Expr::List(items) => InternedKind::List(
            items
                .iter()
                .map(|item| intern_expr(item, symbols))
                .collect(),
        ),
        lim::Expr::Quote(value)
        | lim::Expr::QuasiQuote(value)
        | lim::Expr::Unquote(value)
        | lim::Expr::UnquoteSplicing(value) => {
            InternedKind::Unary(Box::new(intern_expr(value, symbols)))
        }
        other => InternedKind::Other(other.clone()),
    }
}

fn ast_symbol_stats(nodes: &[lim::SpannedExpr]) -> (usize, usize, usize) {
    fn visit_expr<'a>(
        expression: &'a lim::Expr,
        counts: &mut HashMap<&'a str, usize>,
        bytes: &mut usize,
    ) {
        match expression {
            lim::Expr::Symbol(text) => {
                *counts.entry(text).or_default() += 1;
                *bytes += text.len();
            }
            lim::Expr::List(items) => {
                for item in items {
                    visit_expr(item, counts, bytes);
                }
            }
            lim::Expr::Quote(value)
            | lim::Expr::QuasiQuote(value)
            | lim::Expr::Unquote(value)
            | lim::Expr::UnquoteSplicing(value) => visit_expr(value, counts, bytes),
            lim::Expr::Labeled { expression, .. } => visit_expr(expression, counts, bytes),
            _ => {}
        }
    }
    fn visit<'a>(
        node: &'a lim::SpannedExpr,
        counts: &mut HashMap<&'a str, usize>,
        bytes: &mut usize,
    ) {
        visit_expr(&node.expr, counts, bytes);
        for child in &node.children {
            visit(child, counts, bytes);
        }
    }
    let mut counts = HashMap::new();
    let mut bytes = 0;
    for node in nodes {
        visit(node, &mut counts, &mut bytes);
    }
    let occurrences: usize = counts.values().sum();
    let duplicate_allocations = occurrences.saturating_sub(counts.len());
    let unique_bytes = counts.keys().map(|text| text.len()).sum();
    (
        duplicate_allocations,
        bytes.saturating_sub(unique_bytes),
        unique_bytes,
    )
}

fn report_parsed_symbols(label: &str, source: &str) {
    let parsed = lim::parse(source).expect("benchmark syntax parses");
    let (duplicates, repeated_bytes, unique_bytes) = ast_symbol_stats(&parsed);
    println!(
        "{label}.ast-identifiers symbol_nodes={} duplicate_allocations_est={duplicates} repeated_text_bytes={repeated_bytes} unique_text_bytes={unique_bytes}",
        count_ast_symbols(&parsed)
    );
}

fn count_ast_symbols(nodes: &[lim::SpannedExpr]) -> usize {
    fn count_expr(expression: &lim::Expr) -> usize {
        match expression {
            lim::Expr::Symbol(_) => 1,
            lim::Expr::List(items) => items.iter().map(count_expr).sum(),
            lim::Expr::Quote(value)
            | lim::Expr::QuasiQuote(value)
            | lim::Expr::Unquote(value)
            | lim::Expr::UnquoteSplicing(value) => count_expr(value),
            lim::Expr::Labeled { expression, .. } => count_expr(expression),
            _ => 0,
        }
    }
    fn visit(node: &lim::SpannedExpr) -> usize {
        count_expr(&node.expr) + node.children.iter().map(visit).sum::<usize>()
    }
    nodes.iter().map(visit).sum()
}

fn generated_syntax(aliases: usize) -> String {
    (0..aliases)
        .map(|index| format!("(#type Generated{index} #u64)\n"))
        .collect()
}

fn report_generated_symbols(label: &str, source: &str) {
    let nodes = lim::parse(source).expect("benchmark generated syntax parses");
    let (duplicates, repeated_bytes, unique_bytes) = ast_symbol_stats(&nodes);
    let occurrences = count_ast_symbols(&nodes);
    println!(
        "{label}.generated-syntax-est forms={} identifier_nodes={occurrences} duplicate_allocations_est={duplicates} repeated_text_bytes={repeated_bytes} unique_text_bytes={unique_bytes}",
        source.lines().count()
    );
}

fn report_cache_decisions(label: &str, report: &str) {
    let mut decisions = HashMap::<&str, usize>::new();
    for event in report.split("\"decision\":\"").skip(1) {
        if let Some(decision) = event.split('\"').next() {
            *decisions.entry(decision).or_default() += 1;
        }
    }
    println!("{label}.cache-decisions {decisions:?}");
}

fn benchmark_ast_interning(label: &str, source: &str, iterations: usize) {
    let parsed = lim::parse(black_box(source)).unwrap();
    let (duplicates, repeated_bytes, unique_bytes) = ast_symbol_stats(&parsed);
    println!(
        "{label}.ast-symbols duplicate_allocations_est={duplicates} repeated_text_bytes={repeated_bytes} unique_text_bytes={unique_bytes}"
    );
    report_allocations(&format!("{label}.alloc-current-parse"), iterations, || {
        black_box(lim::parse(black_box(source)).unwrap());
    });
    report_allocations(
        &format!("{label}.alloc-parse-plus-intern"),
        iterations,
        || {
            let ast = lim::parse(black_box(source)).unwrap();
            let mut symbols = LocalSymbols::default();
            let interned = ast
                .iter()
                .map(|node| intern_node(node, &mut symbols))
                .collect::<Vec<_>>();
            black_box((&interned, &symbols.by_text));
        },
    );
    report_mirror_allocations(
        &format!("{label}.alloc-interned-mirror"),
        source,
        iterations,
    );
    report_parsed_symbols(label, source);
    let parsed = lim::parse(source).unwrap();
    let mut symbols = LocalSymbols::default();
    for node in &parsed {
        let _ = intern_node(node, &mut symbols);
    }
    println!(
        "{label}.local-interner unique={} lookup_hits={}",
        symbols.by_text.len(),
        count_ast_symbols(&parsed).saturating_sub(symbols.by_text.len())
    );
    // Cold includes parsing and construction of a fresh pool; warm repeats the
    // same operation after the allocator/hash tables have been exercised.
    for (temperature, rounds) in [("cold", 1), ("warm", iterations)] {
        measure(&format!("{label}.ast-intern-{temperature}"), rounds, || {
            let ast = lim::parse(black_box(source)).unwrap();
            let mut symbols = LocalSymbols::default();
            let interned = ast
                .iter()
                .map(|node| intern_node(node, &mut symbols))
                .collect::<Vec<_>>();
            black_box((&interned, &symbols.by_text));
        });
    }
    measure(&format!("{label}.ast-parse-current"), iterations, || {
        black_box(lim::parse(black_box(source)).unwrap());
    });
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
        source.push_str(&format!(
            "(#fn work-{index} () #u64 (#return {index}u64))\n"
        ));
    }
    source.push_str("(#fn main () #u64 (#return 42u64))\n");
    source
}

fn generator_program(aliases: usize) -> String {
    let mut source = String::from(
        "(#gn aliases (pairs) (#gn-for-each pair pairs (#gn-list (#gn-symbol \"#type\") (#gn-first pair) (#gn-first (#gn-rest pair)))))\n(#generate aliases (",
    );
    for index in 0..aliases {
        source.push_str(&format!("(Generated{index} #u64) "));
    }
    source.push_str("))\n(#fn main () #u64 (#return 42u64))\n");
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
    let intern_only = env::args().any(|argument| argument == "--intern-only");
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
    benchmark_ast_interning("generated-256", &large, iterations);
    benchmark_ast_interning(
        "large_reference_projections",
        include_str!("../examples/large_reference_projections.lim"),
        iterations,
    );
    benchmark_ast_interning(
        "vec_allocator",
        include_str!("../examples/vec_allocator.lim"),
        iterations,
    );
    if intern_only {
        fs::remove_dir_all(root).unwrap();
        return;
    }

    let shared_path = root.join("shared.lim");
    fs::write(&shared_path, "(#type SharedMarker #u64)\n").unwrap();
    for (label, source) in [("small", &small), ("large", &large)] {
        report_symbol_repetition(label, source);
        let tokens = lim::lex(source).unwrap();
        let symbol_iterations = iterations.max(200);
        measure(&format!("{label}.symbol-clones"), symbol_iterations, || {
            black_box(clone_symbol_text(black_box(&tokens)));
        });
        measure(
            &format!("{label}.symbol-intern-pilot"),
            symbol_iterations,
            || {
                black_box(intern_symbol_text(black_box(&tokens)));
            },
        );
        measure(&format!("{label}.lex"), iterations, || {
            black_box(lim::lex(black_box(source)).unwrap());
        });
        measure(&format!("{label}.parse"), iterations, || {
            black_box(lim::parse(black_box(source)).unwrap());
        });
        let project_source = format!(
            "(#import \"shared.lim\")\n(#cfg-if (#cfg-is #platform linux) (#fn cfg-enabled () #u64 (#return 1u64)))\n{source}"
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
        let (_, cold_report) = lim::with_cache_report(|| {
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
        report_cache_decisions(&format!("{label}.generator-cold"), &cold_report);
        let generated = generated_syntax(aliases);
        report_generated_symbols(&format!("{label}.generator-cold"), &generated);
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
        let (_, warm_report) = lim::with_cache_report(|| {
            lim::write_generated_sources_from_path_with_config_and_cache(
                &generator_source,
                &generator_path,
                &generated_dir,
                &config,
                &cache_dir,
            )
            .unwrap();
        });
        report_cache_decisions(&format!("{label}.generator-warm"), &warm_report);
        report_generated_symbols(&format!("{label}.generator-warm"), &generated);
    }
    if let Ok(status) = fs::read_to_string("/proc/self/status") {
        if let Some(peak) = status.lines().find(|line| line.starts_with("VmHWM:")) {
            println!("process_peak_memory: {peak}");
        }
    }

    let mut chain = String::from("(#fn step-0 () #u64 (#return 42u64))\n");
    for index in 1..64 {
        chain.push_str(&format!(
            "(#fn step-{index} () #u64 (#return (#if true (#call step-{} (:)) 0u64)))\n",
            index - 1
        ));
    }
    chain.push_str("(#fn main () #u64 (#return (#call step-63 (:))))");
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
