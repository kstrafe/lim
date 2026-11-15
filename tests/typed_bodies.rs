mod support;
use std::fs;

#[test]
fn imported_named_operands_keep_exact_spans_in_the_ir() {
    let scratch = support::Scratch::new("typed-import");
    let module = "#fn add {\n  #params = ((left #u32) (right #u32));\n  #returns = #u32;\n  #body = ( (#return (#u32::add-wrap left right))\n  );\n}\n#fn value {\n  #params = ();\n  #returns = #u32;\n  #body = ( (#return (#call add ((right 2) (left 40))))\n  );\n}\n";
    fs::write(scratch.path().join("module.lim"), module).unwrap();
    let source =
        "#alias ext@value = ./module.lim::value\n#fn main {\n  #params = ();\n  #returns = #u32;\n  #body = ( (#return (#call ext@value ()))\n  );\n}\n";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let checked = lim::CheckedProgram::validate(&program).unwrap();
    let dump = checked.dump_typed_ir();
    assert!(
        dump.contains("argument source order: [1, 0]"),
        "missing imported call-site order: {dump}"
    );
    for literal in ["2", "40"] {
        let offset = module.rfind(&format!(" {literal}")).unwrap() + 1;
        assert!(
            dump.lines()
                .any(|line| line.contains(&format!("Integer({literal})"))
                    && line.contains(&format!("start: {offset},"))
                    && line.contains("Some(U32)")),
            "missing exact imported span: {dump}"
        );
    }
}

#[test]
fn aggregate_property_errors_underline_the_offending_property() {
    let scratch = support::Scratch::new("linear-annotation");
    for (source, expected, token) in [
        (
            "#enum Token (#unknown) ()\n",
            "aggregate properties",
            "#unknown",
        ),
        (
            "#struct Token (#linear #linear) ()\n",
            "duplicate aggregate property",
            "#linear",
        ),
    ] {
        let error = lim::compile_source_to_assembly(
            source,
            &scratch.path().join("bad.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.message.contains(expected), "{}", error.message);
        let span = error.span.unwrap();
        assert_eq!(span.start, source.rfind(token).unwrap(), "{source}");
        assert_eq!(&source[span.start..span.end], token);
        assert!(lim::render_diagnostic(&error, source, "bad.lim").contains('^'));
    }
}
