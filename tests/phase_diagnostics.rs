use std::fs;

#[test]
fn phase_errors_keep_paths_ranges_and_message_metadata_separate() {
    let directory = std::env::temp_dir().join(format!("lim-phase-spans-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("root: with spaces.lim");
    let imported = directory.join("module: with spaces.lim");
    let cache = directory.join("cache");
    let config = lim::CompileConfig::default();
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let root = "#alias Byte = \"./module: with spaces.lim::Byte\"\n";
    fs::write(&path, root).unwrap();
    let source =
        "#cfg-if (#cfg-and (#cfg-is #platform linux) (#cfg-is #unknown yes)) (#type Byte #u8)\n";
    fs::write(&imported, source).unwrap();
    let error = lim::compile_source_to_assembly(root, &path, &config, &cache, target).unwrap_err();
    assert_eq!(error.source_name.as_deref(), imported.to_str());
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#unknown");

    let source = "#gn fail () (#gn-error \"ordinary text; source span 0:0:1; source file /not/the/source: 8:2: bad\")\n#generate fail\n";
    fs::write(&imported, source).unwrap();
    for _ in 0..2 {
        let error =
            lim::compile_source_to_assembly(root, &path, &config, &cache, target).unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Generator);
        assert_eq!(error.source_name.as_deref(), imported.to_str());
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "#generate fail\n");
        assert!(error.message.contains("source file /not/the/source"));
    }
    let source =
        "#fn value () #u64 (#return 42u64)\n#const bad #u64 (#u64::add-wrap 1u64 (#call value ()))\n";
    let error =
        lim::compile_source_to_assembly(source, &path, &config, &cache, target).unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Codegen);
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "(#call value ())");
    assert!(!error.message.contains("source span"));

    let source =
        "#gn inner () `((#fn bad () #u64 (#return false)))\n#gn outer () `((#generate inner))\n#generate outer\n";
    let cold = lim::compile_source_to_assembly(source, &path, &config, &cache, target).unwrap_err();
    let warm = lim::compile_source_to_assembly(source, &path, &config, &cache, target).unwrap_err();
    assert_eq!(cold, warm);
    assert!(cold.span.is_some());
    assert!(!cold.expansion_provenance.is_empty());
    fs::remove_dir_all(directory).unwrap();
}
