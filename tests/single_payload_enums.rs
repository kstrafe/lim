mod support;

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("single-payload-enums");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join(".lim/cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn generated_and_distributed_variants_cannot_bypass_the_single_payload_rule() {
    for source in [
        "#gn emit () `((#enum Bad () ((Bad.Pair #u64 #u32))))\n#generate emit\n",
        "#distributed-enum Bad ()\n#enum-contribute Bad (Bad.Pair #u64 #u32)\n",
    ] {
        let error = compile(source).unwrap_err();
        assert!(
            error.message.contains("at most one payload type"),
            "{error:?}"
        );
        assert!(error.span.is_some(), "{error:?}");
    }
}

#[test]
fn every_pinned_payload_projection_is_indexless_and_rejects_the_old_form() {
    for (operator, reference, borrow) in [
        ("#pin-get-payload-unchecked", "#pin-ref", "#pin-borrow"),
        (
            "#pin-get-payload-unchecked-mut",
            "#pin-ref-mut",
            "#pin-borrow-mut",
        ),
    ] {
        let source = format!(
            "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                 (#let-mut owner Choice (Choice.Full 42u64))
                 (#let value ({reference} #u64)
                   (#unsafe ({operator} ({borrow} owner) Choice.Full)))
                 (#return (#deref value))\n  );\n}}\n"
        );
        compile(&source).unwrap();
        let indexed = source.replace("owner) Choice.Full)", "owner) Choice.Full 0)");
        let error = compile(&indexed).unwrap_err();
        assert!(
            error.message.contains("expects 2 operands"),
            "{operator}: {error:?}"
        );
        assert!(error.span.is_some(), "{operator}: {error:?}");
    }
}

#[test]
fn a_fieldless_variant_has_no_pinned_payload_to_borrow() {
    let error = compile(
        "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut owner Choice Choice.Empty)
             (#let value (#pin-ref #u64)
               (#unsafe (#pin-get-payload-unchecked (#pin-borrow owner) Choice.Empty)))
             (#return (#deref value))\n  );\n}\n",
    )
    .unwrap_err();
    assert!(error.message.contains("no payload"), "{error:?}");
}
