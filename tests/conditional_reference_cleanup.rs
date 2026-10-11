mod support;

use std::{process::Command, time::Duration};

const DECLARATIONS: &str = "
  (#struct Resource (: value #u64)) (#linear Resource)
  (#enum Holder ((Holding (#ref Resource)) (Plain #u64))) (#linear Holder)
  (#enum Cell ((Empty) (Full Holder))) (#linear Cell)
  (#struct Output (: cell Cell)) (#linear Output)
  (#fn extract (: source (#ref-mut Cell)) Output
    (#let old Cell (#deref source))
    (#deref-set source (Empty))
    (#return (#struct-literal Output (: cell old))))
  (#fn inspect (: output Output) #u64
    (#let (Output cell) Output output)
    (#return (#match cell
      (#case (Empty) 42u64)
      (#case (Full holder) (#match holder
        (#case (Holding held) (#get held value))
        (#case (Plain amount) amount))))))";

fn run(source: &str, label: &str) {
    let scratch = support::Scratch::new(label);
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &path,
            &lim::CompileConfig::default(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"))
    };
    let cold = compile();
    let warm = compile();
    assert_eq!(cold, warm);
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &warm,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn ordinary_extraction_retains_nested_reference_and_reference_free_alternatives() {
    for initializer in [
        "(Empty)",
        "(Full (Holding (#borrow owner)))",
        "(Full (Plain 42u64))",
    ] {
        let source = format!(
            "{DECLARATIONS}
          (#fn main () #u64
            (#let owner Resource (#struct-literal Resource (: value 42u64)))
            (#let-mut cell Cell {initializer})
            (#let result #u64 (#call inspect
              (: output (#call extract (: source (#borrow-mut cell))))))
            (#assert (#variant-is (#borrow cell) Empty))
            (#forget cell) (#forget owner) (#return result))"
        );
        run(&source, "ordinary-conditional-reference-extraction");
    }
}

#[test]
fn extracted_reference_cannot_hide_a_live_loan_of_its_owner() {
    let source = format!(
        "{DECLARATIONS}
      (#fn main () #u64
        (#let owner Resource (#struct-literal Resource (: value 42u64)))
        (#let-mut cell Cell (Full (Holding (#borrow owner))))
        (#let output Output (#call extract (: source (#borrow-mut cell))))
        (#forget owner)
        (#let answer #u64 (#call inspect (: output output)))
        (#forget cell) (#return answer))"
    );
    let scratch = support::Scratch::new("ordinary-extracted-reference-conflict");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("extraction must not erase the real owner's live borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some(), "{error:?}");
}

#[test]
fn lifetime_only_pointer_anchor_cannot_prove_extracted_storage_absent_or_consumed() {
    let source = format!(
        "{DECLARATIONS}
      (#fn opaque-extract (: anchor (#ref-mut Cell) : address (#ptr-mut Cell)) #u64
        (#let view (#ref-mut Cell) (#unsafe (#ptr-borrow-mut anchor address)))
        (#return (#call inspect (: output (#call extract (: source view))))))"
    );
    let scratch = support::Scratch::new("ordinary-pointer-extraction-no-permission");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("a lifetime anchor is not permission to consume the pointed-to cell");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
    let span = error.span.expect("unresolved inputs have a source span");
    assert_eq!(
        &source[span.start..span.end],
        "(#call inspect (: output (#call extract (: source view))))",
    );
}
