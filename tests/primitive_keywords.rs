mod support;
use lim::{parse_program, Type};

fn reject(source: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new("primitive-keywords");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

const PRIMITIVES: &[&str] = &[
    "bool", "char", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128",
    "usize", "f32", "f64",
];

#[test]
fn every_primitive_type_requires_a_prefix() {
    for name in PRIMITIVES {
        let source = format!("#fn identity ((value #{name})) #{name} (#return value)\n");
        assert!(parse_program(&source).is_ok(), "{name}");
        let source = format!("#fn identity ((value {name})) #{name} (#return value)\n");
        let error = reject(&source);
        assert!(error.message.contains(&format!("#{name}")), "{error:?}");
        let span = error.span.expect("primitive error has a source span");
        assert_eq!(&source[span.start..span.end], *name);
        assert_eq!(Type::from_name(&format!("#{name}")), Type::from_name(name));
    }
}

#[test]
fn nested_type_positions_are_checked_without_rewriting_identifiers_or_literals() {
    for ty in ["(#ref u8)", "(#array u8 4)", "(#slice u8)", "(#ptr u8)"] {
        let source = format!("#struct Data () ((value {ty}))\n");
        let error = reject(&source);
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "u8");
    }
    assert!(parse_program("#fn make-u64 () #u64 (#return (#u64::add-wrap 40u64 2u64))\n").is_ok());
    assert!(parse_program("#struct User::Type () ((field-name #u8))\n").is_ok());
}
