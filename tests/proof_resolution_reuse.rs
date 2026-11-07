mod support;

use lim::{check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode};
use std::fs;

fn check(
    source: &str,
    path: &std::path::Path,
    theorem: &str,
) -> Result<lim::CheckedTheorem, lim::Diagnostic> {
    check_theorem_details_from_path_with_config(source, path, &CompileConfig::default(), theorem)
}

#[test]
fn missing_and_malformed_contract_theorem_lists_are_rejected() {
    let path = std::path::Path::new("proof-using.lim");
    let missing = check(
        "(#theorem selected (#proof-using (absent) true))",
        path,
        "selected",
    )
    .expect_err("a missing theorem dependency must fail");
    assert_eq!(missing.code, DiagnosticCode::ProofInvalid, "{missing:?}");
    assert!(missing.message.contains("absent"), "{}", missing.message);

    for source in [
        "(#theorem selected (#proof-using ((#proof-eq true true)) true))",
        "(#theorem selected (#proof-using (true) true))",
    ] {
        let error = check(source, path, "selected")
            .expect_err("malformed and non-symbol dependency entries must fail");
        assert!(
            matches!(
                error.code,
                DiagnosticCode::ProofInvalid | DiagnosticCode::Type
            ),
            "{error:?}"
        );
    }
}

#[test]
fn alias_to_imported_contract_theorem_is_a_valid_dependency() {
    let scratch = support::Scratch::new("proof-resolution-reuse");
    let library_dir = scratch.path().join("facade");
    fs::create_dir(&library_dir).unwrap();
    let implementation_path = library_dir.join("impl.lim");
    fs::write(
        &implementation_path,
        r#"
          (#fn identity (: value #u8) #u8 (#return value))
          (#theorem identity-contract
            (#proof-contract identity true
              (#proof-eq (#proof-result) (#proof-old value))))
        "#,
    )
    .unwrap();
    let library_path = library_dir.join("lib.lim");
    fs::write(
        &library_path,
        r#"
          (#std)
          (#alias identity = ./impl.lim::identity)
          (#alias identity-contract = ./impl.lim::identity-contract)
          (#export identity identity-contract)
        "#,
    )
    .unwrap();
    let entry_path = scratch.path().join("main.lim");
    let source = r#"
      (#std)
      (#alias imported-contract = ./facade/lib.lim::identity-contract)
      (#alias imported-identity = ./facade/lib.lim::identity)
      (#theorem selected
        (#proof-using (imported-contract)
          (#proof-contract imported-identity true
            (#proof-eq (#proof-result) (#proof-old value)))))
    "#;
    fs::write(&entry_path, source).unwrap();
    check(source, &entry_path, "selected").unwrap_or_else(|error| panic!("{}", error.message));
    check(
        "(#theorem selected (#proof-using (./facade/lib.lim::identity-contract) true))",
        &entry_path,
        "selected",
    )
    .unwrap_or_else(|error| panic!("direct theorem file reference: {}", error.message));

    let private = format!(
        "(#std) (#alias private-contract = {}::identity-contract) (#theorem selected (#proof-using (private-contract) true))",
        implementation_path.display()
    );
    let error = check(&private, &entry_path, "selected")
        .expect_err("an absolute reference cannot bypass the facade export");
    assert!(
        error.message.contains("private library implementation")
            || error.message.contains("not exported"),
        "{}",
        error.message
    );
}
