mod support;
use std::{fs, process::Command, time::Duration};

#[test]
fn reports_hits_misses_damage_and_dependency_identity_separately() {
    let scratch = support::Scratch::new("cache-report");
    let root = scratch.path();
    let input = root.join("main.lim");
    let source = "(#gn-fn answer () 42) (#gn value () `((#const Answer u64 ,(#gn-call answer)))) (@value) (@optional (: type u64 : name Maybe)) (#fn main () u64 (#return Answer))";
    fs::write(&input, &source).unwrap();
    let run = |cfg: &str| {
        let (status, out, err) = support::run(
            Command::new(env!("CARGO_BIN_EXE_lim"))
                .arg("--explain-cache")
                .arg(&input)
                .args(["--cfg", cfg, "--diagnostic-format=json"]),
            Duration::from_secs(5),
            1024 * 1024,
        )
        .unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&err));
        assert!(err.is_empty());
        String::from_utf8(out).unwrap()
    };
    let cold = run("mode=one");
    assert!(cold.contains("missing-entry"));
    assert!(cold.contains("key_material"));
    let warm = run("mode=one");
    assert!(warm.contains("hit"));
    assert!(!warm.contains("missing-entry"));
    assert!(run("mode=two").contains("missing-entry"));
    fs::write(&input, source.replace("42", "43")).unwrap();
    assert!(run("mode=one").contains("missing-entry"));
    for entry in fs::read_dir(root.join(".lim/cache")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|extension| extension == "lim") {
            fs::write(path, "(#type Edited u8)").unwrap();
        }
    }
    assert!(run("mode=one").contains("invalid-entry"));
}
