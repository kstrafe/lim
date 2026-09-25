mod support;
use std::{collections::BTreeMap, fs, path::Path, process::Command, time::Duration};

fn snapshot(root: &Path, directory: &Path, output: &mut BTreeMap<String, Vec<u8>>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            snapshot(root, &path, output);
        } else {
            output.insert(
                path.strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned(),
                fs::read(path).unwrap(),
            );
        }
    }
}

#[test]
fn cold_and_warm_builds_are_identical_across_relocated_workspaces() {
    let left = support::Scratch::new("repro-left");
    let right = support::Scratch::new("repro-right");
    let mut expected = None;
    for root in [left.path(), right.path()] {
        fs::write(root.join("module.lim"), "(#const Z u64 2u64) (#const A u64 20u64) (#const Float f64 1.5f64)\n(#generator alias (name) `((#type ,name u64)))\n(@alias Word)\n(@optional u64 Maybe)").unwrap();
        fs::write(
            root.join("main.lim"),
            "(#import \"module.lim\") (#fn main () u64 (#return (#u64.+.wrap A Z)))",
        )
        .unwrap();
        for _ in 0..2 {
            for arguments in [
                vec!["--emit-asm", "main.lim", "program.s"],
                vec!["main.lim", "-o", "program"],
            ] {
                let result = support::run(
                    Command::new(env!("CARGO_BIN_EXE_lim"))
                        .current_dir(root)
                        .args(arguments),
                    Duration::from_secs(20),
                    1024 * 1024,
                )
                .unwrap();
                assert!(result.0.success(), "{}", String::from_utf8_lossy(&result.2));
            }
            let result = support::run(
                &mut Command::new(root.join("program")),
                Duration::from_secs(2),
                1024,
            )
            .unwrap();
            assert_eq!(result.0.code(), Some(22));
            let mut actual = BTreeMap::new();
            snapshot(root, &root.join(".lim"), &mut actual);
            actual.insert(
                "program.s".into(),
                fs::read(root.join("program.s")).unwrap(),
            );
            actual.insert("program".into(), fs::read(root.join("program")).unwrap());
            if let Some(expected) = &expected {
                let expected: &BTreeMap<String, Vec<u8>> = expected;
                assert_eq!(
                    actual.keys().collect::<Vec<_>>(),
                    expected.keys().collect::<Vec<_>>()
                );
                for (path, contents) in &actual {
                    assert_eq!(contents, &expected[path], "artifact differs: {path}");
                }
            } else {
                expected = Some(actual);
            }
        }
    }
}
