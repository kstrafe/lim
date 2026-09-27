use std::{fs, process::Command};

// Independent, dependency-free JSON grammar validator for emitted records.
fn json_value(bytes: &[u8], cursor: &mut usize) {
    fn whitespace(bytes: &[u8], cursor: &mut usize) {
        while bytes.get(*cursor).is_some_and(u8::is_ascii_whitespace) {
            *cursor += 1;
        }
    }
    whitespace(bytes, cursor);
    match bytes[*cursor] {
        b'"' => {
            *cursor += 1;
            while bytes[*cursor] != b'"' {
                assert!(bytes[*cursor] >= 32);
                if bytes[*cursor] == b'\\' {
                    *cursor += 1;
                    match bytes[*cursor] {
                        b'u' => {
                            for _ in 0..4 {
                                *cursor += 1;
                                assert!(bytes[*cursor].is_ascii_hexdigit());
                            }
                        }
                        b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {}
                        _ => panic!("invalid JSON escape"),
                    }
                }
                *cursor += 1;
            }
            *cursor += 1;
        }
        start @ (b'{' | b'[') => {
            *cursor += 1;
            let end = if start == b'{' { b'}' } else { b']' };
            whitespace(bytes, cursor);
            if bytes[*cursor] != end {
                loop {
                    if start == b'{' {
                        assert_eq!(bytes[*cursor], b'"');
                        json_value(bytes, cursor);
                        whitespace(bytes, cursor);
                        assert_eq!(bytes[*cursor], b':');
                        *cursor += 1;
                    }
                    json_value(bytes, cursor);
                    whitespace(bytes, cursor);
                    if bytes[*cursor] == end {
                        break;
                    }
                    assert_eq!(bytes[*cursor], b',');
                    *cursor += 1;
                    whitespace(bytes, cursor);
                }
            }
            *cursor += 1;
        }
        b't' => {
            assert_eq!(&bytes[*cursor..*cursor + 4], b"true");
            *cursor += 4;
        }
        b'f' => {
            assert_eq!(&bytes[*cursor..*cursor + 5], b"false");
            *cursor += 5;
        }
        b'n' => {
            assert_eq!(&bytes[*cursor..*cursor + 4], b"null");
            *cursor += 4;
        }
        b'0'..=b'9' => {
            while bytes.get(*cursor).is_some_and(u8::is_ascii_digit) {
                *cursor += 1;
            }
        }
        _ => panic!("invalid JSON value"),
    }
    whitespace(bytes, cursor);
}

#[test]
fn errors_are_json_from_frontend_through_linker() {
    let directory = std::env::temp_dir().join(format!("lim-json-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("quoted \"é: input.lim");
    for (source, category) in [
        ("(#fn main () u64 (#return \"bad)", "lex"),
        ("(#fn main () u64 (#return 0u64)", "parse"),
        (
            "(#fn main () u64 (#let café u64 false) (#return café))",
            "type",
        ),
        ("(#fn main () u64 (#return 42u64))", "link"),
        (
            "(#gn fail () (#gn-error \"bad \\\"message\\\"\")) (@fail)",
            "generator",
        ),
    ] {
        fs::write(&path, source).unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .arg("--diagnostic-format=json")
            .arg(&path)
            .arg("-o")
            .arg(directory.join("output"));
        if category == "link" {
            command.args(["--link-lib", "lim_missing_json_test_library"]);
        }
        let output = command.output().unwrap();
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert_eq!(stderr.lines().count(), 1, "{stderr}");
        let mut cursor = 0;
        json_value(stderr.as_bytes(), &mut cursor);
        assert_eq!(cursor, stderr.len());
        assert!(
            stderr.contains(&format!("\"category\":\"{category}\"")),
            "{stderr}"
        );
        assert!(stderr.contains("\"schema_version\":1"));
        if category != "link" {
            assert!(stderr.contains("\"primary\":true"), "{stderr}");
        }
    }
    let imported = directory.join("module.lim");
    fs::write(&imported, "(#fn broken () u64 (#return false))").unwrap();
    fs::write(&path, "(#import \"module.lim\")").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--diagnostic-format=json")
        .arg(&path)
        .output()
        .unwrap();
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(text.contains("module.lim"), "{text}");
    fs::write(
        &path,
        "(#gn bad () `((#fn broken () u64 (#return false)))) (@bad)",
    )
    .unwrap();
    let mut previous = None;
    for _ in 0..2 {
        let output = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg("--diagnostic-format=json")
            .arg(&path)
            .output()
            .unwrap();
        let text = String::from_utf8(output.stderr).unwrap();
        assert!(!text.contains("\"expansion_provenance\":[]"), "{text}");
        if let Some(previous) = &previous {
            assert_eq!(&text, previous);
        }
        previous = Some(text);
    }
    fs::remove_dir_all(directory).unwrap();
}
