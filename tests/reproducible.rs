mod support;
use std::{collections::BTreeMap, fs, path::Path, process::Command, time::Duration};

fn snapshot(root: &Path, directory: &Path, output: &mut BTreeMap<String, Vec<u8>>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            // Semantic summaries deliberately include physical source paths in
            // their context key. Check their warm stability per workspace below;
            // they are not location-independent generated/build artifacts.
            if path == root.join(".lim/cache/semantic") {
                continue;
            }
            snapshot(root, &path, output);
        } else {
            let mut contents = fs::read(&path).unwrap();
            if path
                .extension()
                .is_some_and(|extension| extension == "hash")
            {
                // Source checksums include invocation-location comments, which
                // intentionally differ after relocating a workspace. Verify
                // integrity independently rather than comparing those hashes.
                let key = fs::read(path.with_extension("key")).unwrap();
                let source = fs::read(
                    root.join(".lim/generated")
                        .join(path.file_name().unwrap())
                        .with_extension("lim"),
                )
                .unwrap();
                let mut hash = 0x6c62272e07bb014262b821756295c58du128;
                for byte in key.iter().chain([0].iter()).chain(source.iter()) {
                    hash ^= u128::from(*byte);
                    hash = hash.wrapping_mul(0x0000000001000000000000000000013bu128);
                }
                assert_eq!(contents, format!("{hash:032x}").as_bytes());
                contents = b"verified source checksum".to_vec();
            } else if path.extension().is_some_and(|extension| extension == "key")
                && contents.get(32) == Some(&b'\n')
            {
                // Per-invocation metadata combines the source checksum and
                // full key. Check the location-dependent checksum before
                // normalizing it, just as for the builtin .hash sidecars.
                let metadata = String::from_utf8(contents).unwrap();
                let (checksum, key) = metadata.split_once('\n').unwrap();
                let source = fs::read(
                    root.join(".lim/generated")
                        .join(path.file_name().unwrap())
                        .with_extension("lim"),
                )
                .unwrap();
                let mut hash = 0x6c62272e07bb014262b821756295c58du128;
                for byte in key.as_bytes().iter().chain([0].iter()).chain(source.iter()) {
                    hash ^= u128::from(*byte);
                    hash = hash.wrapping_mul(0x0000000001000000000000000000013bu128);
                }
                assert_eq!(checksum, format!("{hash:032x}"));
                contents = format!("verified source checksum\n{key}").into_bytes();
            } else if path.extension().is_some_and(|extension| extension == "lim") {
                // Normalize only provenance comments, never executable source.
                let source = String::from_utf8(contents).unwrap();
                let prefix = format!("// {}/", root.display());
                contents = source.replace(&prefix, "// <workspace>/").into_bytes();
            }
            output.insert(
                path.strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned(),
                contents,
            );
        }
    }
}

fn normalized_text(root: &Path, bytes: &[u8]) -> Vec<u8> {
    let text = String::from_utf8(bytes.to_vec()).unwrap();
    let root = root.to_string_lossy();
    let mut encoded_root = String::new();
    for byte in root.bytes() {
        if byte.is_ascii_alphanumeric() {
            encoded_root.push(char::from(byte));
        } else {
            encoded_root.push_str(&format!("_x{byte:02x}_"));
        }
    }
    text.replace(root.as_ref(), "<workspace>")
        .replace(&encoded_root, "<workspace>")
        .into_bytes()
}

fn normalized_generated_text(root: &Path, bytes: &[u8]) -> Vec<u8> {
    let normalized = String::from_utf8(normalized_text(root, bytes)).unwrap();
    let mut output = String::with_capacity(normalized.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut pending_space = false;
    for ch in normalized.chars() {
        if in_string {
            output.push(ch);
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
        } else if ch == '"' {
            if pending_space && !output.is_empty() {
                output.push(' ');
            }
            pending_space = false;
            in_string = true;
            output.push(ch);
        } else if ch.is_whitespace() {
            pending_space = true;
        } else {
            if pending_space && !output.is_empty() {
                output.push(' ');
            }
            pending_space = false;
            output.push(ch);
        }
    }
    output.into_bytes()
}

fn portable_snapshot(root: &Path, actual: &BTreeMap<String, Vec<u8>>) -> BTreeMap<String, Vec<u8>> {
    let mut portable = BTreeMap::new();
    let mut generated = actual
        .iter()
        .filter(|(path, _)| path.starts_with(".lim/generated/") && path.ends_with(".lim"))
        .map(|(_, contents)| normalized_generated_text(root, contents))
        .collect::<Vec<_>>();
    generated.sort();

    for (path, contents) in actual {
        if path.starts_with(".lim/cache/generated-")
            || (path.starts_with(".lim/generated/") && path.ends_with(".lim"))
        {
            continue;
        }
        let normalized = if path.ends_with(".s") {
            normalized_text(root, contents)
        } else {
            contents.clone()
        };
        portable.insert(path.clone(), normalized);
    }
    for (index, contents) in generated.into_iter().enumerate() {
        portable.insert(format!(".lim/generated/source-{index}.lim"), contents);
    }
    portable
}

#[test]
fn cold_and_warm_builds_are_identical_across_relocated_workspaces() {
    let left = support::Scratch::new("repro-left");
    let right = support::Scratch::new("repro-right");
    let mut expected_portable = None;
    let mut expected_binary = None;
    for root in [left.path(), right.path()] {
        let mut expected_summaries = None;
        let mut expected_warm_artifacts = None;
        fs::write(root.join("module.lim"), "(#const z #u64 2u64) (#const a #u64 20u64) (#const float #f64 1.5f64)\n(#gn alias (name) `((#type ,name #u64)))\n(#generate alias Word)\n(#generate #optional (: type #u64 : name Maybe))").unwrap();
        fs::write(
            root.join("main.lim"),
            "(#alias a = ./module.lim::a) (#alias z = ./module.lim::z) (#fn main () #u64 (#return (#u64::add-wrap a z)))",
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
            let mut summaries = BTreeMap::new();
            snapshot(root, &root.join(".lim/cache/semantic"), &mut summaries);
            assert!(
                !summaries.is_empty(),
                "the semantic cache must be exercised"
            );
            if let Some(expected_summaries) = &expected_summaries {
                assert_eq!(
                    &summaries, expected_summaries,
                    "warm builds must preserve the workspace's semantic artifacts"
                );
            } else {
                expected_summaries = Some(summaries);
            }
            if let Some(expected_warm_artifacts) = &expected_warm_artifacts {
                assert_eq!(
                    &actual, expected_warm_artifacts,
                    "cold and warm artifacts must be byte-identical in one workspace"
                );
            } else {
                expected_warm_artifacts = Some(actual.clone());
            }

            let binary = actual.get("program").unwrap();
            if let Some(expected_binary) = &expected_binary {
                assert_eq!(binary, expected_binary, "relocated executable bytes differ");
            } else {
                expected_binary = Some(binary.clone());
            }

            let portable = portable_snapshot(root, &actual);
            if let Some(expected_portable) = &expected_portable {
                assert_eq!(
                    &portable, expected_portable,
                    "relocated build artifacts differ after normalizing workspace paths and generated cache identities"
                );
            } else {
                expected_portable = Some(portable);
            }
        }
    }
}
