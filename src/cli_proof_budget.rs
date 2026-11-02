use lim::ProofBudget;

pub fn parse(arguments: &[String]) -> Result<(Vec<String>, ProofBudget), String> {
    let mut work = None;
    let mut phase_bytes = None;
    let mut total_bytes = None;
    let mut rest = Vec::with_capacity(arguments.len());
    let mut index = 0;
    while index < arguments.len() {
        let option = arguments[index].as_str();
        let slot = match option {
            "--proof-work" => &mut work,
            "--proof-phase-bytes" => &mut phase_bytes,
            "--proof-total-bytes" => &mut total_bytes,
            _ => {
                rest.push(arguments[index].clone());
                // Preserve another option's operand, including a malformed
                // operand beginning with '-'. Its owning parser must reject
                // it, rather than repairing it by stripping budget flags.
                if matches!(
                    option,
                    "--report"
                        | "--emit-proof"
                        | "--cfg"
                        | "--target"
                        | "--module-path"
                        | "-o"
                        | "--link-lib"
                        | "--link-object"
                ) {
                    if let Some(value) = arguments.get(index + 1) {
                        rest.push(value.clone());
                        index += 1;
                    }
                }
                index += 1;
                continue;
            }
        };
        if slot.is_some() {
            return Err(format!("duplicate {option} option"));
        }
        let value = arguments
            .get(index + 1)
            .ok_or_else(|| format!("{option} requires a positive decimal integer"))?;
        let number = parse_positive(value)
            .ok_or_else(|| format!("{option} requires a positive ASCII-decimal integer"))?;
        *slot = Some(number);
        index += 2;
    }
    let default = ProofBudget::default();
    let budget = ProofBudget::new(
        work.unwrap_or(default.work()),
        phase_bytes.unwrap_or(default.phase_bytes()),
        total_bytes.unwrap_or(default.total_bytes()),
    )?;
    Ok((rest, budget))
}

fn parse_positive(value: &str) -> Option<usize> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    value.parse::<usize>().ok().filter(|number| *number > 0)
}

pub fn is_default(budget: ProofBudget) -> bool {
    budget == ProofBudget::default()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    #[test]
    fn defaults_and_valid_flags() {
        let (rest, budget) = parse(&args(&[
            "input",
            "--proof-work",
            "42",
            "--proof-phase-bytes",
            "99",
            "--proof-total-bytes",
            "100",
        ]))
        .unwrap();
        assert_eq!(rest, args(&["input"]));
        assert_eq!(
            (budget.work(), budget.phase_bytes(), budget.total_bytes()),
            (42, 99, 100)
        );
        let (_, defaults) = parse(&args(&["input"])).unwrap();
        assert!(is_default(defaults));
    }

    #[test]
    fn rejects_duplicate_and_malformed_values() {
        for values in [
            args(&["--proof-work", "1", "--proof-work", "2"]),
            args(&["--proof-work"]),
            args(&["--proof-work", "0"]),
            args(&["--proof-work", "１２"]),
            args(&["--proof-work", "+1"]),
            args(&["--proof-work", "184467440737095516160"]),
        ] {
            assert!(parse(&values).is_err(), "accepted {values:?}");
        }
    }

    #[test]
    fn budget_flags_cannot_repair_another_options_missing_operand() {
        for option in ["--report", "--cfg", "--target", "--module-path"] {
            let source = args(&[option, "--proof-work", "1000000", "value"]);
            let (rest, budget) = parse(&source).unwrap();
            assert_eq!(rest, source);
            assert!(is_default(budget));
        }
    }
}
