//! Three pinned generic GCD theorem replays from Lean's upstream library.
mod support;
use lim::{
    check_lean_export, check_lean_export_with_policy,
    lsp::json::{self, Json},
    translate_lean_export_with_policy, LeanFoundationPolicy,
};
use std::{collections::BTreeMap, fs, process::Command, time::Duration};

const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;
const TARGETS: [&str; 3] = [
    "GcdSource.zeroLeft",
    "GcdSource.successor",
    "GcdSource.zeroRight",
];
fn basis(target: &str) -> &'static [&'static str] {
    match target {
        "GcdSource.zeroLeft" | "GcdSource.successor" => &["Quot.sound"],
        "GcdSource.zeroRight" => &["Quot.sound", "propext"],
        _ => panic!("unknown target"),
    }
}
fn artifacts() -> (String, String) {
    let r = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    (
        fs::read_to_string(r.join("tests/fixtures/lean_export_gcd/gcd.ndjson")).unwrap(),
        fs::read_to_string(r.join("theorems/lean_replay/gcd.lim")).unwrap(),
    )
}
fn rows(s: &str) -> Vec<Json> {
    s.lines().map(|l| json::parse(l).unwrap()).collect()
}
fn object(v: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(m) = v else {
        panic!("expected object")
    };
    m
}
fn render(v: &[Json]) -> String {
    v.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}

#[test]
fn raw_api_and_native_translation_preserve_each_target_closure() {
    let (raw, native) = artifacts();
    assert!(check_lean_export(raw.as_bytes(), TARGETS[2])
        .unwrap_err()
        .message
        .contains("not authorized"));
    let all = check_lean_export_with_policy(raw.as_bytes(), TARGETS[2], POLICY).unwrap();
    assert_eq!(all.declarations.len(), 284);
    assert_eq!(all.axioms, ["Quot.sound", "propext"]);
    assert_eq!(all.target_axioms, basis(TARGETS[2]));
    assert_eq!(all.foundations, ["quotient-computation-v1"]);
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/gcd.lim");
    for target in TARGETS {
        let report = check_lean_export_with_policy(raw.as_bytes(), target, POLICY).unwrap();
        assert_eq!(report.declarations.len(), 284);
        assert_eq!(report.axioms, ["Quot.sound", "propext"]);
        assert_eq!(report.target_axioms, basis(target));
        assert_eq!(report.foundations, ["quotient-computation-v1"]);
        let translated = translate_lean_export_with_policy(raw.as_bytes(), target, POLICY).unwrap();
        assert!(native.contains(&format!("(#theorem {}\n", translated.target)));
        if target == TARGETS[2] {
            assert_eq!(translated.source, native);
        }
        let checked = lim::check_theorem_details_from_path_with_config(
            &native,
            &path,
            &lim::CompileConfig::default(),
            &translated.target,
        )
        .unwrap();
        assert_eq!(checked.foundations, basis(target));
    }
}

#[test]
fn cli_audits_all_targets_exactly_with_empty_path() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let (raw, native) = artifacts();
    let rp = root.join("tests/fixtures/lean_export_gcd/gcd.ndjson");
    let np = root.join("theorems/lean_replay/gcd.lim");
    assert!(!raw.is_empty() && !native.is_empty());
    let mut c = Command::new(env!("CARGO_BIN_EXE_lim"));
    c.env("PATH", "")
        .args(["--check-lean-export", rp.to_str().unwrap(), TARGETS[2]]);
    let (s, out, err) = support::run(&mut c, Duration::from_secs(30), 65536).unwrap();
    assert!(!s.success());
    assert!(out.is_empty());
    assert!(String::from_utf8_lossy(&err).contains("not authorized"));
    for target in TARGETS {
        let mut c = Command::new(env!("CARGO_BIN_EXE_lim"));
        c.env("PATH", "").args([
            "--check-lean-export",
            rp.to_str().unwrap(),
            target,
            "--lean-foundations",
        ]);
        let (s, out, err) = support::run(&mut c, Duration::from_secs(30), 65536).unwrap();
        assert!(s.success(), "{}", String::from_utf8_lossy(&err));
        let expected = [
            format!("checked Lean export theorem {target} (284 declarations)"),
            "declared Lean axioms: Quot.sound, propext".to_owned(),
            format!("target logical foundations: {}", basis(target).join(", ")),
        ];
        assert_eq!(
            String::from_utf8(out).unwrap().lines().collect::<Vec<_>>(),
            expected.iter().map(String::as_str).collect::<Vec<_>>()
        );
        let translated = translate_lean_export_with_policy(raw.as_bytes(), target, POLICY).unwrap();
        let mut c = Command::new(env!("CARGO_BIN_EXE_lim"));
        c.env("PATH", "").args([
            "--check-theorem",
            np.to_str().unwrap(),
            translated.target.as_str(),
        ]);
        let (s, out, err) = support::run(&mut c, Duration::from_secs(30), 65536).unwrap();
        assert!(s.success(), "{}", String::from_utf8_lossy(&err));
        let expected = [
            format!("checked theorem {}", translated.target),
            format!("logical foundations: {}", basis(target).join(", ")),
        ];
        assert_eq!(
            String::from_utf8(out).unwrap().lines().collect::<Vec<_>>(),
            expected.iter().map(String::as_str).collect::<Vec<_>>()
        );
    }
}

#[test]
fn helper_renaming_preserves_all_three_target_bases_and_axiom_identity_is_fixed() {
    let (raw, _) = artifacts();
    let mut data = rows(&raw);
    let mut count = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "gcd" => "renamedGcd".into(),
            "_unary" => "renamedUnary".into(),
            "fix" => "ordinaryFix".into(),
            "casesOn" => "ordinaryCasesOn".into(),
            s if s.starts_with("gcd.") => format!("renamed{}", s),
            s if s.starts_with("_unary.") => format!("renamed{}", s),
            _ => continue,
        };
        *part = Json::String(replacement);
        count += 1;
    }
    assert!(count > 0);
    let renamed = render(&data);
    for target in TARGETS {
        let r = check_lean_export_with_policy(renamed.as_bytes(), target, POLICY).unwrap();
        assert_eq!(r.target_axioms, basis(target));
    }
    let mut bad = rows(&raw);
    let ax = bad.iter_mut().find(|r| r.get("axiom").is_some()).unwrap();
    object(object(ax).get_mut("axiom").unwrap()).insert("name".into(), Json::Number("0".into()));
    assert!(check_lean_export_with_policy(render(&bad).as_bytes(), TARGETS[2], POLICY).is_err());
}

#[test]
fn each_corrupted_raw_target_proof_fails_after_valid_prefix() {
    let (raw, _) = artifacts();
    let checked = check_lean_export_with_policy(raw.as_bytes(), TARGETS[2], POLICY).unwrap();
    for target_name in TARGETS {
        let mut data = rows(&raw);
        let target = checked
            .declarations
            .iter()
            .find(|d| d.name == target_name)
            .unwrap();
        let at = target.line - 1;
        let wrong = data[..at]
            .iter()
            .find_map(|r| {
                r.get("sort")
                    .and_then(Json::integer)
                    .map(|_| r.get("ie").unwrap().clone())
            })
            .unwrap();
        object(object(&mut data[at]).get_mut("thm").unwrap()).insert("value".into(), wrong);
        let e = check_lean_export_with_policy(render(&data).as_bytes(), target_name, POLICY)
            .unwrap_err();
        assert_eq!(e.line, target.line);
        assert!(e.message.contains("type mismatch"), "{}", e.message);
    }
}

#[test]
fn corrupted_gcd_defining_equation_is_rejected_at_its_helper_line() {
    let (raw, _) = artifacts();
    let checked = check_lean_export_with_policy(raw.as_bytes(), TARGETS[2], POLICY).unwrap();
    let helper = checked
        .declarations
        .iter()
        .find(|d| d.name.contains("Nat.gcd._unary.eq_def"))
        .expect("GCD defining-equation helper in checked report");
    let mut data = rows(&raw);
    let at = helper.line - 1;
    let wrong = data[..at]
        .iter()
        .find_map(|r| {
            r.get("sort")
                .and_then(Json::integer)
                .map(|_| r.get("ie").unwrap().clone())
        })
        .expect("an existing sort expression before the helper");
    let declaration = &mut data[at];
    let fields = object(declaration);
    let payload = if fields.contains_key("thm") {
        fields.get_mut("thm").unwrap()
    } else {
        fields
            .get_mut("def")
            .expect("helper theorem or definition row")
    };
    object(payload).insert("value".into(), wrong);

    let e =
        check_lean_export_with_policy(render(&data).as_bytes(), TARGETS[2], POLICY).unwrap_err();
    assert_eq!(e.line, helper.line);
    assert!(e.message.contains("type mismatch"), "{}", e.message);
    assert!(!e.message.contains("resource limit"), "{}", e.message);
}

#[test]
fn each_native_proof_is_selected_structurally_and_prefix_remains_valid() {
    let (raw, native) = artifacts();
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/gcd.lim");
    for target in TARGETS {
        let t = translate_lean_export_with_policy(raw.as_bytes(), target, POLICY).unwrap();
        let node = lim::parse(&native)
            .unwrap()
            .into_iter()
            .find(|node| {
                matches!(&node.expr, lim::Expr::List(items)
                    if matches!(items.get(1), Some(lim::Expr::Symbol(name))
                        if name == &t.target))
            })
            .unwrap();
        let clause = node
            .children
            .iter()
            .find(|node| {
                matches!(&node.expr, lim::Expr::List(items)
                    if matches!(items.first(), Some(lim::Expr::Symbol(keyword))
                        if keyword == "#proof"))
            })
            .unwrap();
        let span = clause.children[1].span;
        lim::check_types(&lim::parse_program(&native[..node.span.start]).unwrap()).unwrap();
        let mut changed = native.clone();
        changed.replace_range(span.start..span.end, "#pt-prop");
        let e = lim::check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &lim::CompileConfig::default(),
            &t.target,
        )
        .unwrap_err();
        assert!(e.message.contains("type mismatch"), "{}", e.message);
        assert!(!e.message.contains("resource limit"), "{}", e.message);
    }
}
