mod support;
use std::fs;

#[test]
fn imported_named_operands_keep_exact_spans_in_the_ir() {
    let scratch = support::Scratch::new("typed-import");
    let module = "(#fn add ((left u32) (right u32)) u32 (#return (#u32.+.wrap left right)))\n(#fn value () u32 (#return (#call add (#fn-args (right 2) (left 40)))))";
    fs::write(scratch.path().join("module.lim"), module).unwrap();
    let source = "(#import-external \"module.lim\" ext-) (#fn main () u32 (#return (#call ext-value (#fn-args))))";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let checked = lim::CheckedProgram::validate(&program).unwrap();
    let dump = checked.dump_typed_ir();
    for literal in ["2", "40"] {
        let offset = module.rfind(&format!(" {literal})")).unwrap() + 1;
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
fn linear_annotation_errors_underline_the_actual_annotation() {
    let scratch = support::Scratch::new("linear-annotation");
    for (source, expected, offset) in [
        ("(#linear Missing)", "concrete struct or enum", 9),
        (
            "(#struct Token ())\n(#linear Token)\n(#linear Token)",
            "duplicate #linear",
            44,
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
        assert_eq!(span.start, offset, "{source}");
        assert!(lim::render_diagnostic(&error, source, "bad.lim").contains('^'));
    }
}
