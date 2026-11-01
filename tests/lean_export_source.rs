//! Native proof files are readable translations, independently rechecked.
mod support;

use lim::{translate_lean_export, Expr, Item};

const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

#[test]
fn every_real_export_and_hand_authored_protocol_fixture_translates() {
    let fixtures = [
        (IDENTITY, TARGET),
        (
            include_str!("fixtures/lean_export/inductives.ndjson"),
            "Replay.doubleTwo",
        ),
        (
            include_str!("fixtures/lean_export/mutual.ndjson"),
            "Replay.mutualDepth",
        ),
        (
            include_str!("fixtures/lean_export/real-identity.ndjson"),
            "ReplaySource.identityProof",
        ),
        (
            include_str!("fixtures/lean_export/real-inductives.ndjson"),
            "ReplaySource.doubleTwo",
        ),
        (
            include_str!("fixtures/lean_export/real-projection.ndjson"),
            "ReplaySource.projection",
        ),
        (
            include_str!("fixtures/lean_export/real-mutual.ndjson"),
            "ReplaySource.mutualDepth",
        ),
        (
            include_str!("fixtures/lean_export/real-nested.ndjson"),
            "ReplaySource.nestedCount",
        ),
        (
            include_str!("fixtures/lean_export/real-nested-poly.ndjson"),
            "ReplaySource.polyNested",
        ),
        (
            include_str!("fixtures/lean_export/real-nested-indexed.ndjson"),
            "ReplaySource.indexedNested",
        ),
        (
            include_str!("fixtures/lean_export/real-nested-deep.ndjson"),
            "ReplaySource.deepNested",
        ),
        (
            include_str!("fixtures/lean_export/real-nested-sigma.ndjson"),
            "ReplaySource.sigmaNested",
        ),
    ];
    for (input, target) in fixtures {
        let translated = translate_lean_export(input.as_bytes(), target)
            .unwrap_or_else(|why| panic!("{target}: {why}"));
        assert_eq!(translated.report.target, target);
        let parsed = lim::parse_program(&translated.source).unwrap();
        lim::check_types(&parsed).unwrap();
        assert_eq!(parsed.items.len(), translated.report.declarations.len());
        assert!(parsed
            .items
            .iter()
            .all(|item| matches!(item, Item::Proof { .. })));
        for declaration in &translated.report.declarations {
            assert!(translated.source.contains(&declaration.sha256));
        }
        let scratch = support::Scratch::new("lean-source-theorem");
        lim::check_theorem_from_path_with_config(
            &translated.source,
            &scratch.path().join("translated.lim"),
            &lim::CompileConfig::default(),
            &translated.target,
        )
        .unwrap();
    }
}

#[test]
fn translation_is_deterministic_and_canonical_target_identity_is_preserved() {
    let first = translate_lean_export(IDENTITY.as_bytes(), TARGET).unwrap();
    let identity = &first
        .report
        .declarations
        .iter()
        .find(|d| d.kind == "theorem")
        .unwrap()
        .identity;
    let second = translate_lean_export(IDENTITY.as_bytes(), identity).unwrap();
    assert_eq!(first.source, second.source);
    assert_eq!(first.target, second.target);
    assert_eq!(first.report.render_json(), second.report.render_json());
    assert!(first.source.contains(&first.report.input_sha256));
}

#[test]
fn ordinary_checker_rejects_tampered_native_evidence_despite_provenance_comments() {
    let translated = translate_lean_export(IDENTITY.as_bytes(), TARGET).unwrap();
    let nodes = lim::parse(&translated.source).unwrap();
    let target = nodes
        .iter()
        .find(|node| {
            matches!(&node.expr, Expr::List(parts)
        if matches!(parts.get(1),Some(Expr::Symbol(name)) if name == &translated.target))
        })
        .unwrap();
    let proof = target.children.last().unwrap().children[1].span;
    let damaged = format!(
        "{}#pt-zero{}",
        &translated.source[..proof.start],
        &translated.source[proof.end..]
    );
    let program = lim::parse_program(&damaged).unwrap();
    let why = lim::check_types(&program).unwrap_err();
    assert!(why.contains("type mismatch"), "{why}");
}

#[test]
fn opaque_initializers_are_retained_but_do_not_become_transparent() {
    let input = IDENTITY.replace("\"def\":", "\"opaque\":").replace(
        "\"hints\":\"abbrev\",\"safety\":\"safe\",",
        "\"isUnsafe\":false,",
    );
    let translated = translate_lean_export(input.as_bytes(), TARGET).unwrap();
    let program = lim::parse_program(&translated.source).unwrap();
    let name = program
        .items
        .iter()
        .find_map(|item| match item {
            Item::Proof {
                name,
                proposition: Expr::List(parts),
            } if matches!(parts.first(),Some(Expr::Symbol(head)) if head == "#proof-opaque") => {
                Some(name)
            }
            _ => None,
        })
        .unwrap();
    let forged = format!("{}\n(#theorem opaque-is-zero (#universes) (#parameters) (#statement (#pt-eq #pt-nat (#pt-app (#pt-use {name} (1)) #pt-nat #pt-zero) #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))",translated.source);
    let program = lim::parse_program(&forged).unwrap();
    assert!(lim::check_types(&program)
        .unwrap_err()
        .contains("type mismatch"));
}

#[test]
fn source_comments_escape_names_and_colliding_sanitized_names_stay_distinct() {
    let hostile = "Audit\n(#math-opaque injected () #pt-nat #pt-zero)\n;";
    let encoded = lim::lsp::json::Json::String(hostile.into()).render();
    let input = IDENTITY.replace("\"Audit\"", &encoded);
    let translated =
        translate_lean_export(input.as_bytes(), &format!("{encoded}.identity.theorem")).unwrap();
    let program = lim::parse_program(&translated.source).unwrap();
    assert_eq!(program.items.len(), 2);
    assert!(!program
        .items
        .iter()
        .any(|item| matches!(item,Item::Proof{name,..} if name=="injected")));

    let before = "{\"def\":{\"name\":2";
    let prefix = "A".repeat(70);
    let extra = format!("{{\"str\":{{\"pre\":0,\"str\":\"{prefix}y\"}},\"in\":5}}\n{{\"def\":{{\"name\":5,\"levelParams\":[4],\"type\":4,\"value\":7,\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[5]}}}}\n");
    let input = IDENTITY
        .replace("\"Audit\"", &format!("\"{prefix}x\""))
        .replace(before, &format!("{extra}{before}"));
    let translated =
        translate_lean_export(input.as_bytes(), &format!("{prefix}x.identity.theorem")).unwrap();
    let program = lim::parse_program(&translated.source).unwrap();
    let names = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Proof { name, .. } => Some(name),
            _ => None,
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(names.len(), 3);
    assert!(names.iter().all(|name| name.ends_with(&"A".repeat(64))));
}

#[test]
fn all_input_records_must_validate_before_source_is_returned() {
    for input in [
        format!("{IDENTITY}{{\"axiom\":{{}}}}\n"),
        format!("{IDENTITY}{{bad json}}\n"),
    ] {
        assert!(translate_lean_export(input.as_bytes(), TARGET).is_err());
    }
}

#[test]
fn typed_lets_under_binders_keep_outer_reference_meanings() {
    let input = IDENTITY.replace("{\"def\":",concat!(
        "{\"letE\":{\"name\":0,\"type\":2,\"value\":5,\"body\":2,\"nondep\":false},\"ie\":20}\n",
        "{\"lam\":{\"name\":0,\"type\":1,\"body\":20,\"binderInfo\":\"default\"},\"ie\":21}\n",
        "{\"lam\":{\"name\":0,\"type\":0,\"body\":21,\"binderInfo\":\"implicit\"},\"ie\":22}\n{\"def\":"))
        .replace("\"type\":4,\"value\":7","\"type\":4,\"value\":22");
    let translated = translate_lean_export(input.as_bytes(), TARGET).unwrap();
    let compact = translated
        .source
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        compact.contains("(#pt-let (#parameter v2 v0) v1 v1)"),
        "{}",
        translated.source
    );
    lim::check_types(&lim::parse_program(&translated.source).unwrap()).unwrap();
}
