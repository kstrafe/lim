use std::{fs, process::Command};

#[test]
fn competing_workers_claim_state_exactly_once() {
    let root = std::env::temp_dir().join(format!("lim-cas-threads-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let source = include_str!("../examples/atomic_claim.lim");
    let assembly = lim::compile_source_to_assembly(
        source,
        &root.join("input.lim"),
        &lim::CompileConfig::default(),
        &root.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = root.join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    for _ in 0..20 {
        assert_eq!(Command::new(&binary).status().unwrap().code(), Some(42));
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn exchange_and_compare_exchange_cover_all_atomic_widths_and_orders() {
    let root = std::env::temp_dir().join(format!("lim-cas-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    for ty in [
        "#u8", "#u16", "#u32", "#u64", "#usize", "#i8", "#i16", "#i32", "#i64",
    ] {
        let suffix = ty.trim_start_matches('#');
        let initial = if suffix.starts_with('i') {
            format!("-1{suffix}")
        } else {
            format!("17{suffix}")
        };
        let source = format!("#fn main () #u64
            (#let-mut state (#atomic {ty}) (#atomic-init {ty} {initial}))
            (#let old {ty} (#atomic-exchange (#borrow state) 2{suffix} #memory-relaxed))
            (#assert ({ty}::eq old {initial}))
            (#let (#tuple won observed) (#tuple #bool {ty}) (#atomic-compare-exchange (#borrow state) 2{suffix} {initial} #memory-acq-rel #memory-acquire))
            (#assert won) (#assert ({ty}::eq observed 2{suffix}))
            (#let (#tuple failed actual) (#tuple #bool {ty}) (#atomic-compare-exchange-weak (#borrow state) 0{suffix} 3{suffix} #memory-seq-cst #memory-seq-cst))
            (#assert (#bool::eq failed false)) (#assert ({ty}::eq actual {initial}))
            (#let (#tuple weak-won weak-old) (#tuple #bool {ty}) (#atomic-compare-exchange-weak (#borrow state) {initial} 42{suffix} #memory-release #memory-relaxed))
            (#assert weak-won) (#assert ({ty}::eq weak-old {initial}))
            (#forget state) (#return 42u64)\n");
        let path = root.join(format!("{ty}.lim"));
        let assembly = lim::compile_source_to_assembly(
            &source,
            &path,
            &lim::CompileConfig::default(),
            &root.join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{ty}: {}", error.message));
        assert!(assembly.contains("lock cmpxchg"));
        let binary = root.join(ty);
        lim::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        assert_eq!(
            Command::new(binary).status().unwrap().code(),
            Some(42),
            "{ty}"
        );
    }
    for success in ["relaxed", "acquire", "release", "acq-rel", "seq-cst"] {
        for failure in ["relaxed", "acquire", "release", "acq-rel", "seq-cst"] {
            let source = format!("#fn main () () (#let-mut state (#atomic #u64) (#atomic-init #u64 0u64)) (#atomic-compare-exchange (#borrow state) 0u64 1u64 #memory-{success} #memory-{failure}) (#forget state) (#return ())\n");
            let allowed = failure == "relaxed"
                || (failure == "acquire" && matches!(success, "acquire" | "acq-rel" | "seq-cst"))
                || (failure == "seq-cst" && success == "seq-cst");
            let program = lim::parse_program(&source).unwrap();
            assert_eq!(
                lim::check_types(&program).is_ok(),
                allowed,
                "{success}/{failure}"
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}
