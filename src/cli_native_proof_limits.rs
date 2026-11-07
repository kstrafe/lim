use lim::NativeProofLimits;

pub fn parse(arguments: &[String]) -> Result<(Vec<String>, NativeProofLimits), String> {
    let mut values: [Option<usize>; 6] = [None; 6];
    let mut max_scratch_bytes = None;
    let mut rest = Vec::with_capacity(arguments.len());
    let mut index = 0;

    while index < arguments.len() {
        let option = arguments[index].as_str();
        if option == "--native-proof-scratch-bytes" {
            if max_scratch_bytes.is_some() {
                return Err(format!("duplicate {option} option"));
            }
            let value = arguments
                .get(index + 1)
                .ok_or_else(|| format!("{option} requires a positive ASCII-decimal integer"))?;
            max_scratch_bytes =
                Some(parse_positive_u64(value).ok_or_else(|| {
                    format!("{option} requires a positive ASCII-decimal integer")
                })?);
            index += 2;
            continue;
        }
        let field = match option {
            "--native-proof-bytes" => Some(0),
            "--native-proof-declarations" => Some(1),
            "--native-proof-directory-bytes" => Some(2),
            "--native-proof-render-nodes" => Some(3),
            "--native-proof-correspondence-nodes" => Some(4),
            "--native-proof-correspondence-bytes" => Some(5),
            _ => None,
        };

        if let Some(field) = field {
            let value = arguments
                .get(index + 1)
                .ok_or_else(|| format!("{option} requires a positive ASCII-decimal integer"))?;
            let parsed = parse_positive_usize(value)
                .ok_or_else(|| format!("{option} requires a positive ASCII-decimal integer"))?;
            if values[field].is_some() {
                return Err(format!("duplicate {option} option"));
            }
            values[field] = Some(parsed);
            index += 2;
            continue;
        }

        rest.push(arguments[index].clone());
        if preserves_operand(option) {
            if let Some(value) = arguments.get(index + 1) {
                rest.push(value.clone());
                index += 1;
            }
        }
        index += 1;
    }

    let defaults = NativeProofLimits::default();
    let limits = NativeProofLimits {
        max_bytes: values[0].unwrap_or(defaults.max_bytes),
        max_declarations: values[1].unwrap_or(defaults.max_declarations),
        max_directory_bytes: values[2].unwrap_or(defaults.max_directory_bytes),
        max_render_nodes: values[3].unwrap_or(defaults.max_render_nodes),
        max_correspondence_nodes: values[4].unwrap_or(defaults.max_correspondence_nodes),
        max_correspondence_bytes: values[5].unwrap_or(defaults.max_correspondence_bytes),
        max_scratch_bytes: max_scratch_bytes.unwrap_or(defaults.max_scratch_bytes),
    }
    .validate()?;
    Ok((rest, limits))
}

fn preserves_operand(option: &str) -> bool {
    matches!(
        option,
        "--report"
            | "--emit-proof"
            | "--proof-work"
            | "--proof-phase-bytes"
            | "--proof-total-bytes"
            | "--export-bytes"
            | "--export-names"
            | "--export-name-bytes"
            | "--export-levels"
            | "--export-expressions"
            | "--export-declarations"
            | "--export-dependencies"
            | "--export-dependency-bytes"
            | "--export-payload-bytes"
            | "--export-scratch-bytes"
    )
}

fn parse_positive_usize(value: &str) -> Option<usize> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    value.parse::<usize>().ok().filter(|number| *number > 0)
}

fn parse_positive_u64(value: &str) -> Option<u64> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    value.parse::<u64>().ok().filter(|number| *number > 0)
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    #[test]
    fn scratch_capacity_is_explicit_and_preserves_export_operands() {
        let (_, limits) = parse(&args(&["--native-proof-scratch-bytes", "1024"])).unwrap();
        assert_eq!(limits.max_scratch_bytes, 1024);
        for values in [
            args(&["--native-proof-scratch-bytes", "0"]),
            args(&["--native-proof-scratch-bytes", "18446744073709551615"]),
            args(&[
                "--native-proof-scratch-bytes",
                "1",
                "--native-proof-scratch-bytes",
                "2",
            ]),
            args(&["--native-proof-scratch-bytes"]),
        ] {
            assert!(parse(&values).is_err());
        }
        let source = args(&[
            "--export-scratch-bytes",
            "--native-proof-scratch-bytes",
            "100",
        ]);
        let (rest, selected) = parse(&source).unwrap();
        assert_eq!(rest, source);
        assert_eq!(selected, NativeProofLimits::default());
    }

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    #[test]
    fn defaults_and_each_flag_are_applied() {
        let (rest, defaults) = parse(&args(&["input"])).unwrap();
        assert_eq!(rest, args(&["input"]));
        assert_eq!(defaults, NativeProofLimits::default());
        let (rest, limits) = parse(&args(&[
            "input",
            "--native-proof-bytes",
            "1",
            "--native-proof-declarations",
            "2",
            "--native-proof-directory-bytes",
            "3",
            "--native-proof-render-nodes",
            "4",
            "--native-proof-correspondence-nodes",
            "5",
            "--native-proof-correspondence-bytes",
            "6",
        ]))
        .unwrap();
        assert_eq!(rest, args(&["input"]));
        assert_eq!(
            limits,
            NativeProofLimits {
                max_bytes: 1,
                max_declarations: 2,
                max_directory_bytes: 3,
                max_render_nodes: 4,
                max_correspondence_nodes: 5,
                max_correspondence_bytes: 6,
                max_scratch_bytes: 128 * 1024 * 1024,
            }
        );
    }

    #[test]
    fn rejects_invalid_values_missing_values_and_duplicates() {
        for value in ["0", "+1", "-1", "１２", "184467440737095516160"] {
            assert!(
                parse(&args(&["--native-proof-bytes", value])).is_err(),
                "accepted {value:?}"
            );
        }
        assert!(parse(&args(&["--native-proof-bytes"])).is_err());
        assert!(parse(&args(&[
            "--native-proof-bytes",
            "1",
            "--native-proof-bytes",
            "2"
        ]))
        .is_err());
    }

    #[test]
    fn preserves_operands_of_other_options_even_when_they_look_like_flags() {
        let options = [
            "--report",
            "--emit-proof",
            "--proof-work",
            "--proof-phase-bytes",
            "--proof-total-bytes",
            "--export-bytes",
            "--export-names",
            "--export-name-bytes",
            "--export-levels",
            "--export-expressions",
            "--export-declarations",
            "--export-dependencies",
            "--export-dependency-bytes",
            "--export-payload-bytes",
        ];
        for option in options {
            let source = args(&[option, "--native-proof-bytes", "not-a-number"]);
            let (rest, limits) = parse(&source).unwrap();
            assert_eq!(rest, source);
            assert_eq!(limits, NativeProofLimits::default());
        }
        for operand in ["-malformed", "--native-proof-bytes"] {
            let source = args(&["--report", operand, "--native-proof-bytes", "not-a-number"]);
            assert!(
                parse(&source).is_err(),
                "operand was skipped or repaired: {source:?}"
            );
        }
    }
}
