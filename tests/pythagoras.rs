mod support;

use lim::{
    check_proof_artifact_from_path, format_source, parse_program, NativeProofLimits, ProofBudget,
};
use std::{fs, path::Path, process::Command, time::Duration};

const SOURCE: &str = include_str!("../theorems/pythagoras.lim");
const TARGET: &str = "pythagoras-orthogonal";

fn cli(args: &[&str]) -> (std::process::ExitStatus, String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.args(args).env("PATH", "");
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(10), 1024 * 1024).expect("CLI completes");
    (
        status,
        String::from_utf8_lossy(&stdout).into_owned(),
        String::from_utf8_lossy(&stderr).into_owned(),
    )
}

fn matching_paren(source: &str, open: usize) -> usize {
    let bytes = source.as_bytes();
    assert_eq!(bytes[open], b'(');
    let mut depth = 0usize;
    for (index, byte) in bytes.iter().enumerate().skip(open) {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return index + 1;
                }
            }
            _ => {}
        }
    }
    panic!("unclosed expression in theorem source");
}

fn replace_once(source: &str, needle: &str, replacement: &str) -> String {
    assert_eq!(
        source.matches(needle).count(),
        1,
        "mutation anchor must be unique: {needle}"
    );
    source.replacen(needle, replacement, 1)
}

fn theorem_mutation(source: &str, mutate: impl FnOnce(&str) -> String) -> String {
    let start = source
        .find("(#theorem pythagoras-orthogonal")
        .expect("target theorem exists");
    let end = matching_paren(source, start);
    let theorem = mutate(&source[start..end]);
    format!("{}{}{}", &source[..start], theorem, &source[end..])
}

fn rejects(mutated: &str, label: &str) {
    parse_program(mutated)
        .unwrap_or_else(|error| panic!("{label} mutation is not valid Lim: {error}"));
    let scratch = support::Scratch::new(label);
    let path = scratch.path().join("mutated.lim");
    fs::write(&path, mutated).unwrap();
    assert!(
        check_proof_artifact_from_path(
            &path,
            ProofBudget::default(),
            NativeProofLimits::default(),
            TARGET
        )
        .is_err(),
        "accepted mutation: {label}"
    );
}

#[test]
fn pythagoras_is_a_closed_standalone_artifact() {
    let scratch = support::Scratch::new("pythagoras-artifact");
    let path = scratch.path().join("pythagoras.lim");
    fs::write(&path, SOURCE).unwrap();

    let checked = check_proof_artifact_from_path(
        Path::new(&path),
        ProofBudget::default(),
        NativeProofLimits::default(),
        TARGET,
    )
    .expect("standalone kernel checks Pythagoras");
    assert_eq!(checked.name, TARGET);
    assert!(
        checked.foundations.is_empty(),
        "unexpected foundations: {:?}",
        checked.foundations
    );

    let (status, stdout, stderr) = cli(&["--check-theorem", path.to_str().unwrap(), TARGET]);
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout.trim(), format!("checked theorem {TARGET}"));
}

#[test]
fn pythagoras_survives_format_round_trip() {
    let formatted = format_source(SOURCE).expect("format theorem source");
    assert_eq!(format_source(&formatted).unwrap(), formatted);
    let scratch = support::Scratch::new("pythagoras-formatted");
    let path = scratch.path().join("pythagoras-formatted.lim");
    fs::write(&path, formatted).unwrap();
    let checked = check_proof_artifact_from_path(
        &path,
        ProofBudget::default(),
        NativeProofLimits::default(),
        TARGET,
    )
    .expect("formatted artifact remains checkable");
    assert_eq!(checked.name, TARGET);
    assert!(checked.foundations.is_empty());
}

#[test]
fn pythagoras_rejects_missing_assumptions_and_invalid_proofs() {
    let missing_orthogonality = theorem_mutation(SOURCE, |theorem| {
        replace_once(
            theorem,
            "(#parameter orthogonal",
            "(#parameter missing-orthogonal",
        )
    });
    rejects(&missing_orthogonality, "pythagoras-no-orthogonality");

    let missing_symmetry = theorem_mutation(SOURCE, |theorem| {
        replace_once(
            theorem,
            "(#parameter inner-symmetric",
            "(#parameter missing-symmetry",
        )
    });
    rejects(&missing_symmetry, "pythagoras-no-symmetry");

    let missing_bilinearity = theorem_mutation(SOURCE, |theorem| {
        replace_once(
            theorem,
            "(#parameter inner-add-left",
            "(#parameter missing-bilinearity",
        )
    });
    rejects(&missing_bilinearity, "pythagoras-no-bilinearity");

    let wrong_conclusion = theorem_mutation(SOURCE, |theorem| {
        let statement = theorem.find("(#statement").unwrap();
        let proof = theorem.find("(#proof").unwrap();
        let segment = &theorem[statement..proof];
        let changed = replace_once(segment, "inner v)", "inner u)");
        format!("{}{}{}", &theorem[..statement], changed, &theorem[proof..])
    });
    rejects(&wrong_conclusion, "pythagoras-wrong-conclusion");

    let invalid_proof = theorem_mutation(SOURCE, |theorem| {
        let proof_start = theorem.find("(#proof").unwrap() + "(#proof".len();
        let expression_start = theorem[proof_start..].find('(').unwrap() + proof_start;
        let expression_end = matching_paren(theorem, expression_start);
        format!(
            "{}(#pt-refl Scalar zero){}",
            &theorem[..expression_start],
            &theorem[expression_end..]
        )
    });
    rejects(&invalid_proof, "pythagoras-reflexivity-control");
}
