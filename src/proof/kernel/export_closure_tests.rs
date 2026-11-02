//! Synthetic report-graph tests for the audit, not kernel proof inputs.
//! These helpers do not establish or admit theorems. Genuine exported terms
//! exercise the complete checker and this audit in the fixture suite.
use super::*;

fn replay_with_limit(limit: usize) -> Replay {
    let mut replay = Replay::new();
    replay.reports = inventory::Inventory::with_limit(limit);
    replay
}

fn report(replay: &mut Replay, identity: &str, name: &str, kind: &str, dependencies: &[&str]) {
    let id = replay.reports.len();
    replay
        .reports
        .push(LeanDeclarationReport {
            name: name.to_owned(),
            identity: identity.to_owned(),
            kind: kind.to_owned(),
            line: id + 1,
            sha256: "a1".repeat(32),
            dependencies: dependencies
                .iter()
                .map(|value| (*value).to_owned())
                .collect(),
        })
        .unwrap();
    replay.checked.insert(identity, id).unwrap();
}

fn choice_axiom(replay: &mut Replay) {
    report(
        replay,
        "$lean:s6:choice",
        "Classical.choice",
        "axiom",
        &["#pt-foundation-choice"],
    );
}

#[test]
fn direct_and_transitive_foundations_match_declared_axioms() {
    let mut replay = replay_with_limit(usize::MAX);
    choice_axiom(&mut replay);
    report(
        &mut replay,
        "direct",
        "direct",
        "theorem",
        &["$lean:s6:choice"],
    );
    report(
        &mut replay,
        "$lean:s7:propext",
        "propext",
        "axiom",
        &["#pt-foundation-propext"],
    );
    report(
        &mut replay,
        "middle",
        "middle",
        "theorem",
        &["$lean:s7:propext"],
    );
    report(
        &mut replay,
        "transitive",
        "transitive",
        "theorem",
        &["middle"],
    );

    assert_eq!(
        replay.target_axioms("direct").unwrap(),
        ["Classical.choice"]
    );
    assert_eq!(replay.target_axioms("transitive").unwrap(), ["propext"]);
}

#[test]
fn unchecked_targets_and_dependencies_are_errors() {
    let mut replay = replay_with_limit(usize::MAX);
    assert!(replay.target_axioms("missing").is_err());
    report(
        &mut replay,
        "broken",
        "broken",
        "theorem",
        &["missing-dependency"],
    );
    assert!(replay.target_axioms("broken").is_err());
}

#[test]
fn declared_axioms_without_native_foundations_are_rejected() {
    let mut replay = replay_with_limit(usize::MAX);
    report(
        &mut replay,
        "$lean:s6:choice",
        "Classical.choice",
        "axiom",
        &[],
    );
    report(
        &mut replay,
        "target",
        "target",
        "theorem",
        &["$lean:s6:choice"],
    );
    assert!(replay
        .target_axioms("target")
        .unwrap_err()
        .contains("differ"));
}

#[test]
fn native_foundations_without_reachable_declared_axioms_are_rejected() {
    let mut replay = replay_with_limit(usize::MAX);
    report(
        &mut replay,
        "target",
        "target",
        "theorem",
        &["#pt-foundation-choice"],
    );
    assert!(replay
        .target_axioms("target")
        .unwrap_err()
        .contains("differ"));
}

#[test]
fn unsupported_foundation_symbols_are_errors() {
    let mut replay = replay_with_limit(usize::MAX);
    report(
        &mut replay,
        "target",
        "target",
        "theorem",
        &["#pt-foundation-unknown"],
    );
    assert!(replay.target_axioms("target").is_err());
}

#[test]
fn cycles_self_references_and_shared_diamonds_terminate() {
    let mut replay = replay_with_limit(usize::MAX);
    choice_axiom(&mut replay);
    report(
        &mut replay,
        "self",
        "self",
        "theorem",
        &["self", "$lean:s6:choice"],
    );
    report(&mut replay, "left", "left", "theorem", &["shared"]);
    report(&mut replay, "right", "right", "theorem", &["shared"]);
    report(
        &mut replay,
        "shared",
        "shared",
        "theorem",
        &["left", "$lean:s6:choice"],
    );
    assert_eq!(replay.target_axioms("self").unwrap(), ["Classical.choice"]);
    assert_eq!(replay.target_axioms("right").unwrap(), ["Classical.choice"]);
}

#[test]
fn paged_inventory_closure_matches_foundation_labels() {
    let mut replay = replay_with_limit(0);
    choice_axiom(&mut replay);
    for index in 0..4094 {
        let name = format!("node-{index}");
        let dependencies: Vec<String> = if index == 0 {
            vec!["$lean:s6:choice".to_owned()]
        } else {
            vec![format!("node-{}", index - 1), format!("node-{}", index / 2)]
        };
        let refs: Vec<&str> = dependencies.iter().map(String::as_str).collect();
        report(&mut replay, &name, &name, "theorem", &refs);
    }

    assert!(replay.reports.is_spilled());
    assert_eq!(replay.reports.len(), 4095);
    assert_eq!(
        replay.target_axioms("node-4093").unwrap(),
        ["Classical.choice"]
    );
}
