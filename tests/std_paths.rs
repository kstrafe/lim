mod support;

use std::{fs, path::Path, process::Command, time::Duration};

fn compile(root: &Path, source: &str) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &root.join("main.lim"),
        &lim::CompileConfig::default(),
        &root.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn execute(root: &Path, source: &str, expected: i32) {
    let assembly = compile(root, source).unwrap_or_else(|error| panic!("{}", error.message));
    let binary = root.join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        &mut Command::new(binary).env("PATH", ""),
        Duration::from_secs(3),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(expected), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn standard_root_is_embedded_and_cannot_be_shadowed_by_a_project_directory() {
    let scratch = support::Scratch::new("std-root");
    fs::create_dir(scratch.path().join("#std")).unwrap();
    fs::write(
        scratch.path().join("#std/linux_x86_64_syscall_numbers.lim"),
        "#const lINUX-SYS-GETPID #usize 99usize\n",
    )
    .unwrap();
    execute(
        scratch.path(),
        "#alias getpid-number = #std/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPID\n\
        #fn main { #params = {}; #returns = #u64; #body = ((#return (#as getpid-number #u64))); }\n",
        39,
    );
}

#[test]
fn standard_paths_reject_parent_escape_and_unknown_modules_before_filesystem_lookup() {
    let scratch = support::Scratch::new("std-invalid-root");
    for (module, expected) in [
        ("#std/../private.lim", "must stay within #std/"),
        (
            "#std/not-a-shipped-module.lim",
            "unknown standard-library module",
        ),
    ] {
        let source = format!("#alias value = {module}::value\n");
        let error = compile(scratch.path(), &source).unwrap_err();
        assert!(error.message.contains(expected), "{error:?}");
        let span = error.span.expect("invalid paths must have a source range");
        assert!(source[span.start..span.end].contains(module), "{error:?}");
    }
}

const CELL_ARGUMENTS: &str = "{ value-type = #u32; name = Counter; create = make-counter; get = read-counter; set = write-counter; }";

#[test]
fn ordinary_standard_generators_and_local_generators_have_distinct_identities() {
    let scratch = support::Scratch::new("std-cell-identity");
    fs::write(scratch.path().join("application.lim"),
        "#gn cell { name; } `((#type ,name #u64))\n").unwrap();
    let source = format!(
        "#alias standard-cell = #std/cell.lim::cell\n\
        #alias application-cell = ./application.lim::cell\n\
        #generate application-cell {{ name = Local; }}\n\
        #generate standard-cell {CELL_ARGUMENTS}\n\
        #fn main {{ #params = {{}}; #returns = Local; #body = (\n\
          (#let counter Counter (#call make-counter ((value 42u32))))\n\
          (#let answer #u32 (#call read-counter ((cell (#borrow counter)))))\n\
          (#forget counter) (#return (#as answer #u64)) ); }}\n"
    );
    execute(scratch.path(), &source, 42);
}

#[test]
fn direct_standard_generator_calls_and_aliases_share_reordered_cached_inputs() {
    let scratch = support::Scratch::new("std-cell-cache");
    let root = scratch.path();
    let source = format!(
        "#alias cell-factory = #std/cell.lim::cell\n\
        #generate cell-factory {CELL_ARGUMENTS}\n\
        #generate #std/cell.lim::cell {{ set = write-counter; get = read-counter; create = make-counter; name = Counter; value-type = #u32; }}\n\
        #fn main {{ #params = {{}}; #returns = #u64; #body = ((#return 42u64)); }}\n"
    );
    let run = || {
        lim::with_cache_report(|| {
            lim::compile_source_with_generated_sources(
                &source,
                &root.join("main.lim"),
                &lim::CompileConfig::default(),
                &root.join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
                None,
                &root.join("generated"),
            )
        })
    };
    let cold = run().0.unwrap();
    let (warm, report) = run();
    assert_eq!(cold, warm.unwrap());
    assert!(report.contains("\"decision\":\"hit\""), "{report}");
    let artifacts = fs::read_dir(root.join("generated"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "lim")
        })
        .count();
    assert_eq!(
        artifacts, 1,
        "aliases and field order must not create duplicate outputs"
    );
}

#[test]
fn standard_runtime_types_do_not_capture_same_spelled_project_types() {
    let scratch = support::Scratch::new("std-type-identity");
    let source = "#alias StandardString = #std/string.lim::String\n\
        #alias length = #std/string.lim::String::len\n\
        #struct String () ((value #u64))\n\
        #fn standard-length { #params = ((value (#ref StandardString))); #returns = #usize;\n\
          #body = ((#return (#std/string.lim::String::len { string = value; }))); }\n\
        #fn main { #params = {}; #returns = #u64; #body = (\n\
          (#let local String (#struct-literal String ((value 42u64))))\n\
          (#let answer #u64 (#get (#borrow local) value)) (#forget local) (#return answer) ); }\n";
    execute(scratch.path(), source, 42);
}

#[test]
fn ordinary_standard_items_do_not_enable_keyword_named_user_generators() {
    let scratch = support::Scratch::new("std-reserved-generators");
    let error = compile(scratch.path(), "#gn #cell { value; } (#gn-list)\n").unwrap_err();
    assert!(error.message.contains("reserved"), "{error:?}");
}
