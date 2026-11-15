//! Lookup must resolve the actual native compilation artifacts, not snapshots.
mod support;

use std::{fs, path::Path};

fn compile(source: &str, entry: &Path, config: &lim::CompileConfig) {
    let directory = entry.parent().unwrap().join(".lim");
    lim::compile_executable_source_with_generated_sources(
        source,
        entry,
        config,
        &directory.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
        None,
        &directory.join("generated"),
    )
    .unwrap();
}

#[test]
fn async_lookup_reuses_the_native_compilations_exact_generated_file() {
    let scratch = support::Scratch::new("lookup-native-async");
    let entry = scratch.path().join("main.lim");
    let source = "#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
        (function (#fn work ((amount #u64)) #u64 (#return amount))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 0u64)\n  );\n}\n";
    fs::write(&entry, source).unwrap();
    let config = lim::CompileConfig::default();
    compile(source, &entry, &config);
    let directory = scratch.path().join(".lim/generated");
    let original = fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    assert_eq!(original.len(), 1);
    let modified = fs::metadata(&original[0]).unwrap().modified().unwrap();
    let selected = source.find("#return amount").unwrap();
    let located =
        lim::locate_generated(source, &entry, &config, &entry, selected, selected).unwrap();
    assert_eq!(located, original);
    assert_eq!(
        fs::metadata(&located[0]).unwrap().modified().unwrap(),
        modified
    );
    assert!(fs::read_to_string(&located[0])
        .unwrap()
        .contains("Work::poll"));
}

#[test]
fn pin_projection_is_inspectable_safe_generator_code_and_reuses_its_artifact() {
    let scratch = support::Scratch::new("lookup-pin-project");
    let entry = scratch.path().join("main.lim");
    let source = include_str!("../examples/pin_project.lim");
    fs::write(&entry, source).unwrap();
    let config = lim::CompileConfig::default();
    compile(source, &entry, &config);
    let selected = source.find("#generate lim-gen-enum-project").unwrap();
    let located =
        lim::locate_generated(source, &entry, &config, &entry, selected, selected).unwrap();
    assert_eq!(located.len(), 1);
    let generated = fs::read_to_string(&located[0]).unwrap();
    assert!(generated.contains("WorkProjection::project"));
    assert!(generated.contains("#case-pin-mut"));
    assert!(!generated.contains("#unsafe"));
    let modified = fs::metadata(&located[0]).unwrap().modified().unwrap();
    compile(source, &entry, &config);
    assert_eq!(
        fs::metadata(&located[0]).unwrap().modified().unwrap(),
        modified
    );
}

#[test]
fn external_import_lookup_uses_the_prefixed_artifact_from_native_compilation() {
    let scratch = support::Scratch::new("lookup-native-external");
    let entry = scratch.path().join("main.lim");
    let module = scratch.path().join("module.lim");
    let imported = "#generate #optional ((type #u64) (name Value))\n";
    fs::write(&module, imported).unwrap();
    let source = "#alias Ext@Value = ./module.lim::Value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n";
    fs::write(&entry, source).unwrap();
    let config = lim::CompileConfig::default();
    compile(source, &entry, &config);
    let selected = imported.find("#u64").unwrap();
    let located =
        lim::locate_generated(source, &entry, &config, &module, selected, selected).unwrap();
    assert_eq!(located.len(), 1);
    let generated = fs::read_to_string(&located[0]).unwrap();
    assert!(generated.contains("module.lim::Value"), "{generated}");
    assert_eq!(
        fs::read_dir(scratch.path().join(".lim/generated"))
            .unwrap()
            .count(),
        1,
        "lookup must not publish another artifact with a different identity"
    );
}
