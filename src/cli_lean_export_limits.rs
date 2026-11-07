use lim::LeanExportLimits;

pub fn parse(arguments: &[String]) -> Result<(Vec<String>, LeanExportLimits), String> {
    let mut max_bytes = None;
    let mut max_names = None;
    let mut max_name_bytes = None;
    let mut max_levels = None;
    let mut max_expressions = None;
    let mut max_declarations = None;
    let mut max_dependencies = None;
    let mut max_dependency_bytes = None;
    let mut max_payload_bytes = None;
    let mut max_scratch_bytes = None;
    let mut rest = Vec::with_capacity(arguments.len());
    let mut index = 0;

    while index < arguments.len() {
        let option = arguments[index].as_str();
        let field = match option {
            "--export-bytes" => Some(0),
            "--export-names" => Some(1),
            "--export-name-bytes" => Some(2),
            "--export-levels" => Some(3),
            "--export-expressions" => Some(4),
            "--export-declarations" => Some(5),
            "--export-dependencies" => Some(6),
            "--export-dependency-bytes" => Some(7),
            "--export-payload-bytes" => Some(8),
            "--export-scratch-bytes" => Some(9),
            _ => None,
        };

        if let Some(field) = field {
            let value = arguments
                .get(index + 1)
                .ok_or_else(|| format!("{option} requires a positive decimal integer"))?;
            let error = || format!("{option} requires a positive ASCII-decimal integer");
            match field {
                9 => set_value(
                    &mut max_scratch_bytes,
                    parse_positive_u64(value).ok_or_else(error)?,
                    option,
                )?,
                0 => set_value(
                    &mut max_bytes,
                    parse_positive_u64(value).ok_or_else(error)?,
                    option,
                )?,
                1 => set_value(
                    &mut max_names,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                2 => set_value(
                    &mut max_name_bytes,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                3 => set_value(
                    &mut max_levels,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                4 => set_value(
                    &mut max_expressions,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                5 => set_value(
                    &mut max_declarations,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                6 => set_value(
                    &mut max_dependencies,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                7 => set_value(
                    &mut max_dependency_bytes,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                8 => set_value(
                    &mut max_payload_bytes,
                    parse_positive_usize(value).ok_or_else(error)?,
                    option,
                )?,
                _ => unreachable!(),
            }
            index += 2;
            continue;
        }

        rest.push(arguments[index].clone());
        // Keep operands attached to their owning options, even when they look
        // like an export flag or begin with '-'. Their parser must see them.
        if matches!(
            option,
            "--report"
                | "--emit-proof"
                | "--proof-work"
                | "--proof-phase-bytes"
                | "--proof-total-bytes"
                | "--native-proof-bytes"
                | "--native-proof-declarations"
                | "--native-proof-directory-bytes"
                | "--native-proof-render-nodes"
                | "--native-proof-correspondence-nodes"
                | "--native-proof-correspondence-bytes"
                | "--native-proof-scratch-bytes"
        ) {
            if let Some(value) = arguments.get(index + 1) {
                rest.push(value.clone());
                index += 1;
            }
        }
        index += 1;
    }

    let defaults = LeanExportLimits::default();
    let limits = LeanExportLimits {
        max_bytes: max_bytes.unwrap_or(defaults.max_bytes),
        max_names: max_names.unwrap_or(defaults.max_names),
        max_name_bytes: max_name_bytes.unwrap_or(defaults.max_name_bytes),
        max_levels: max_levels.unwrap_or(defaults.max_levels),
        max_expressions: max_expressions.unwrap_or(defaults.max_expressions),
        max_declarations: max_declarations.unwrap_or(defaults.max_declarations),
        max_dependencies: max_dependencies.unwrap_or(defaults.max_dependencies),
        max_dependency_bytes: max_dependency_bytes.unwrap_or(defaults.max_dependency_bytes),
        max_payload_bytes: max_payload_bytes.unwrap_or(defaults.max_payload_bytes),
        max_scratch_bytes: max_scratch_bytes.unwrap_or(defaults.max_scratch_bytes),
    }
    .validate()?;
    Ok((rest, limits))
}

fn set_value<T>(slot: &mut Option<T>, value: T, option: &str) -> Result<(), String> {
    if slot.is_some() {
        return Err(format!("duplicate {option} option"));
    }
    *slot = Some(value);
    Ok(())
}

fn parse_positive_u64(value: &str) -> Option<u64> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    value.parse::<u64>().ok().filter(|number| *number > 0)
}

fn parse_positive_usize(value: &str) -> Option<usize> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    value.parse::<usize>().ok().filter(|number| *number > 0)
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    #[test]
    fn scratch_capacity_is_explicit_and_preserves_native_operands() {
        let (_, limits) = parse(&args(&["--export-scratch-bytes", "1024"])).unwrap();
        assert_eq!(limits.max_scratch_bytes, 1024);
        for values in [
            args(&["--export-scratch-bytes", "0"]),
            args(&["--export-scratch-bytes", "18446744073709551615"]),
            args(&["--export-scratch-bytes", "1", "--export-scratch-bytes", "2"]),
            args(&["--export-scratch-bytes"]),
        ] {
            assert!(parse(&values).is_err());
        }
        let source = args(&[
            "--native-proof-scratch-bytes",
            "--export-scratch-bytes",
            "100",
        ]);
        let (rest, selected) = parse(&source).unwrap();
        assert_eq!(rest, source);
        assert_eq!(selected, LeanExportLimits::default());
    }

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    #[test]
    fn defaults_and_each_flag_are_applied() {
        let (_, defaults) = parse(&args(&[])).unwrap();
        assert_eq!(defaults, LeanExportLimits::default());
        let (rest, limits) = parse(&args(&[
            "input",
            "--export-bytes",
            "1",
            "--export-names",
            "2",
            "--export-name-bytes",
            "3",
            "--export-levels",
            "4",
            "--export-expressions",
            "5",
            "--export-declarations",
            "6",
            "--export-dependencies",
            "7",
            "--export-dependency-bytes",
            "8",
            "--export-payload-bytes",
            "9",
        ]))
        .unwrap();
        assert_eq!(rest, args(&["input"]));
        assert_eq!(
            (
                limits.max_bytes,
                limits.max_names,
                limits.max_name_bytes,
                limits.max_levels,
                limits.max_expressions,
                limits.max_declarations,
                limits.max_dependencies,
                limits.max_dependency_bytes,
                limits.max_payload_bytes
            ),
            (1, 2, 3, 4, 5, 6, 7, 8, 9)
        );
    }

    #[test]
    fn rejects_duplicates_missing_and_malformed_values() {
        for values in [
            args(&["--export-bytes", "1", "--export-bytes", "2"]),
            args(&["--export-names"]),
            args(&["--export-bytes", "0"]),
            args(&["--export-bytes", "１２"]),
            args(&["--export-bytes", "+1"]),
            args(&["--export-bytes", "18446744073709551616"]),
            args(&["--export-names", "18446744073709551616"]),
            args(&["--export-names", "4294967296"]),
        ] {
            assert!(parse(&values).is_err(), "accepted {values:?}");
        }
    }

    #[test]
    fn preserves_malformed_operands_of_other_options() {
        for option in [
            "--report",
            "--emit-proof",
            "--proof-work",
            "--proof-phase-bytes",
            "--proof-total-bytes",
        ] {
            let source = args(&[option, "--export-bytes", "100"]);
            let (rest, limits) = parse(&source).unwrap();
            assert_eq!(rest, source);
            assert_eq!(limits, LeanExportLimits::default());
        }
        for option in ["--report", "--emit-proof", "--proof-work"] {
            let source = args(&[option, "-bad"]);
            assert_eq!(parse(&source).unwrap().0, source);
        }
    }
}
