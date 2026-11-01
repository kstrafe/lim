mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};
use std::fs;

const LIBRARY: &str = r#"
  (#export validate perform)
  (#fn validate (: value (#ref #u64)) #bool
    (#return (#u64::eq (#deref value) 42u64)))
  (#fn perform (: target (#ref #u64)) #u64 (#return (#deref target)))
"#;
const ENTRY: &str = r#"
  (#alias check-value = ./library/lib.lim::validate)
  (#alias do-action = ./library/lib.lim::perform)
  (#fn entry (: input (#ref #u64)) #u64
    (#if (#bool::not (#call check-value (: value input)))
      (#block (#return 0u64)))
    (#return (#call do-action (: target input))))
  (#fn main () #u64
    (#let value #u64 42u64)
    (#return (#call entry (: input (#borrow value)))))
"#;
const CLAIM: &str = "(#theorem validated
  (#proof-requires-validation entry (check-value value) (do-action target)))";

fn compile(source: &str, scratch: &support::Scratch) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

fn fixture() -> support::Scratch {
    let scratch = support::Scratch::new("validation-resolve");
    fs::create_dir(scratch.path().join("library")).unwrap();
    fs::write(scratch.path().join("library/lib.lim"), LIBRARY).unwrap();
    scratch
}

#[test]
fn aliases_preserve_descriptor_labels_and_theorem_adds_no_runtime_code() {
    let scratch = fixture();
    let source = format!("{ENTRY}\n{CLAIM}");
    let path = scratch.path().join("main.lim");
    fs::write(&path, &source).unwrap();
    let with_theorem = compile(&source, &scratch).unwrap();
    assert_eq!(compile(ENTRY, &scratch).unwrap(), with_theorem);
    lim::check_theorem_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "validated",
    )
    .unwrap();
}

#[test]
fn cached_generated_claims_recheck_changes_in_the_calling_program() {
    let scratch = fixture();
    let generator = format!("(#gn make-theorem () `({CLAIM}))\n(#generate make-theorem)");
    let source = format!("{ENTRY}\n{generator}");
    let path = scratch.path().join("main.lim");
    fs::write(&path, &source).unwrap();
    let cold = compile(&source, &scratch).unwrap();
    assert_eq!(compile(&source, &scratch).unwrap(), cold);
    let invalid = source.replace(
        "(#return (#call do-action (: target input)))",
        "(#let other #u64 42u64) (#return (#call do-action (: target (#borrow other))))",
    );
    fs::write(&path, &invalid).unwrap();
    for _ in 0..2 {
        let error = compile(&invalid, &scratch)
            .expect_err("cached theorem trusted a new unvalidated object");
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("same object"), "{}", error.message);
        assert!(error.span.is_some());
    }
}

#[test]
fn validation_fact_limits_cannot_turn_resource_exhaustion_into_a_proof() {
    let mut source = String::from(
        "(#fn validate (: user (#ref #u8)) #bool (#return true))\n\
      (#fn perform (: user (#ref #u8)) () (#return ()))\n(#fn entry () ()\n",
    );
    for index in 0..65 {
        source.push_str(&format!(
            "(#let object{index} #u8 0u8)\n\
            (#call validate (: user (#borrow object{index})))\n"
        ));
    }
    source.push_str("(#return ()))");
    let ordinary = lim::parse_program(&source).unwrap();
    lim::check_types(&ordinary).unwrap();
    for claim in [
        "(#proof-requires-validation entry (validate user) (perform user))",
        "(#proof-not (#proof-requires-validation entry (validate user) (perform user)))",
    ] {
        let parsed = lim::parse_program(&format!("{source}\n(#theorem bounded {claim})")).unwrap();
        let error = lim::check_types(&parsed).expect_err("exhausted trace was certified");
        assert!(
            error.contains("unproved: validation fact budget exhausted"),
            "{error}"
        );
    }
}

#[test]
fn symbolic_indices_check_identity_and_write_overlap_under_path_conditions() {
    for (written, acted, holds) in [
        (
            "(#usize::bit-xor index 1usize)",
            "(#usize::add-wrap index 0usize)",
            true,
        ),
        ("index", "index", false),
        (
            "(#usize::bit-xor index 1usize)",
            "(#usize::bit-xor index 1usize)",
            false,
        ),
    ] {
        let source = format!(
            r#"
          (#fn validate (: user (#ref #u8)) #bool (#return true))
          (#fn perform (: user (#ref #u8)) () (#return ()))
          (#fn entry (: index #usize) ()
            (#if (#usize::ge index 2usize) (#block (#return ())))
            (#let-mut values (#array #u8 2) (#array-of (#array #u8 2) 0u8 0u8))
            (#call validate (: user (#borrow (#index values index))))
            (#set-index values {written} 1u8)
            (#call perform (: user (#borrow (#index values {acted}))))
            (#return ()))
        "#
        );
        lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
        let proof = format!(
            "{source}\n(#theorem index-validation
          (#proof-requires-validation entry (validate user) (perform user)))"
        );
        let result = lim::check_types(&lim::parse_program(&proof).unwrap());
        if holds {
            result.unwrap();
        } else {
            let error = result.expect_err("array element identity or freshness was lost");
            assert!(error.contains("disproved"), "{error}");
        }
    }
}

#[test]
fn observing_a_referenced_child_does_not_invalidate_an_unchanged_parent() {
    let source = r#"
      (#enum Link () ((Link.End) (Link.Next (#ref Node))))
      (#struct Node () (: value #u8 : link Link))
      (#fn validate (: user (#ref Node)) #bool (#return true))
      (#fn perform (: user (#ref Node)) () (#return ()))
      (#fn entry () ()
        (#let child Node (#struct-literal Node (: value 0u8 : link (#enum-literal Link.End))))
        (#let parent Node (#struct-literal Node (: value 0u8
          : link (#enum-literal Link.Next (#borrow child)))))
        (#call validate (: user (#borrow parent)))
        (#call validate (: user (#borrow child)))
        (#call perform (: user (#borrow parent)))
        (#forget parent)
        (#forget child)
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = "(#proof-requires-validation entry (validate user) (perform user))";
    let proved = lim::parse_program(&format!("{source}\n(#theorem preserved {claim})")).unwrap();
    lim::check_types(&proved).unwrap();
    let negated = lim::parse_program(&format!(
        "{source}\n(#theorem impossible (#proof-not {claim}))"
    ))
    .unwrap();
    let error =
        lim::check_types(&negated).expect_err("a non-mutating check manufactured a counterexample");
    assert!(error.contains("disproved"), "{error}");
}
