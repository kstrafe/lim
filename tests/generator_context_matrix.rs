//! Exhaustive small access matrix: producer, caller, unrelated dependency.
mod support;
use std::{fs, path::Path};

fn write(root: &Path, path: &str, source: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn generated_file_access_is_exactly_definition_plus_invocation_not_dependencies() {
    let scratch = support::Scratch::new("generator-context-matrix");
    write(scratch.path(), "producer/lib.lim", "#export make visible\n#fn hidden {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#fn visible {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#gn make (name text) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol text) ()))))\n");
    write(scratch.path(), "third/lib.lim", "#export visible\n#fn hidden {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#fn visible {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n");
    for alias in ["one", "two"] {
        for (file, name, allowed) in [
            ("producer/lib.lim", "hidden", true),
            ("producer/lib.lim", "visible", true),
            ("caller/lib.lim", "hidden", true),
            ("caller/lib.lim", "visible", true),
            ("third/lib.lim", "visible", true),
            ("third/lib.lim", "hidden", false),
        ] {
            // Strings are literal data: manufacture the canonical target explicitly.
            let target = format!("{}::{name}", scratch.path().join(file).display());
            write(scratch.path(), "caller/lib.lim", &format!("#export read visible\n#alias make = ../producer/lib.lim::make\n#alias third-visible = ../third/lib.lim::visible\n#fn hidden {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n#fn visible {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n#generate make read {target:?}\n"));
            let source = format!("#alias {alias} = ./caller/lib.lim::read\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call {alias} ()))\n  );\n}}\n");
            for mode in 0..3 {
                let result = if mode == 0 {
                    lim::parse_program_from_path(&source, &scratch.path().join("main.lim"))
                } else {
                    lim::parse_program_from_path_with_config_and_cache(
                        &source,
                        &scratch.path().join("main.lim"),
                        &lim::CompileConfig::default(),
                        &scratch.path().join(".lim/cache"),
                    )
                }
                .and_then(|program| lim::check_types(&program));
                if allowed {
                    result.unwrap_or_else(|error| panic!("{target}, cache mode {mode}: {error}"));
                } else {
                    let error = result
                        .expect_err("a dependency must not become a third privileged context");
                    assert!(
                        error.contains("private"),
                        "{target}, cache mode {mode}: {error}"
                    );
                }
            }
        }
    }
}

#[test]
fn aliases_share_canonical_caller_authority_but_distinct_files_do_not() {
    let scratch = support::Scratch::new("generator-context-alias-matrix");
    write(scratch.path(), "producer/lib.lim", "#export make\n#gn make (name text) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol text) ()))))\n");
    let target = format!(
        "{}::hidden",
        scratch.path().join("caller/lib.lim").display()
    );
    let caller = format!("#export read\n#alias make = ../producer/lib.lim::make\n#fn hidden {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n#generate make read {target:?}\n");
    write(scratch.path(), "caller/lib.lim", &caller);
    write(scratch.path(), "other/lib.lim", &caller);
    for (second_file, allowed) in [("caller/lib.lim", true), ("other/lib.lim", false)] {
        for order in [["one", "two"], ["two", "one"]] {
            let source = format!("#alias {} = ./caller/lib.lim::read\n#alias {} = ./{second_file}::read\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64::add-wrap (#call one ()) (#call two ())))\n  );\n}}\n", order[0], order[1]);
            for mode in 0..3 {
                let result = if mode == 0 {
                    lim::parse_program_from_path(&source, &scratch.path().join("main.lim"))
                } else {
                    lim::parse_program_from_path_with_config_and_cache(
                        &source,
                        &scratch.path().join("main.lim"),
                        &lim::CompileConfig::default(),
                        &scratch.path().join(".lim/cache"),
                    )
                }
                .and_then(|program| lim::check_types(&program));
                if allowed {
                    result.unwrap_or_else(|error| panic!("{order:?}, cache mode {mode}: {error}"));
                } else {
                    let error = result.expect_err(
                        "a distinct caller cannot use the first caller's private function",
                    );
                    assert!(
                        error.contains("private") && error.contains(&target),
                        "{error}"
                    );
                }
            }
        }
    }
}
