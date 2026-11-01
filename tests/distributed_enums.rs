mod support;

use std::{fs, process::Command, time::Duration};

fn check(source: &str) -> Result<lim::Program, lim::Diagnostic> {
    let program = lim::parse_program(source)
        .map_err(|message| lim::Diagnostic::new(lim::DiagnosticCode::Parse, message))?;
    lim::check_types(&program)
        .map_err(|message| lim::Diagnostic::new(lim::DiagnosticCode::Type, message))?;
    Ok(program)
}

#[test]
fn generated_headers_and_contributions_merge_after_expansion() {
    let source = "(#gn declare (name) `((#distributed-enum ,name (#linear))))
        (#gn contribute (name variant payload)
          `((#enum-contribute ,name (,variant ,payload))))
        (#generate contribute Error Error.Last #u32)
        (#generate declare Error)
        (#generate contribute Error Error.First #u64)
        (#enum-contribute Error (Error.First #u64))
        (#fn main () #u64
          (#let error Error (Error.First 42u64))
          (#return (#match error
            (#case (Error.First value) value)
            (#case (Error.Last value) (#as value #u64)))))";
    let program = check(source).unwrap();
    let (linear, variants) = program
        .items
        .iter()
        .find_map(|item| match item {
            lim::Item::Enum {
                name,
                linear,
                variants,
                ..
            } if name == "Error" => Some((linear, variants)),
            _ => None,
        })
        .unwrap();
    assert!(*linear);
    assert_eq!(
        variants
            .iter()
            .map(|variant| variant.name.as_str())
            .collect::<Vec<_>>(),
        ["Error.First", "Error.Last"]
    );
}

#[test]
fn aliases_and_cache_hits_keep_the_complete_enum() {
    let scratch = support::Scratch::new("distributed-enum-imports");
    let root = scratch.path();
    fs::write(
        root.join("enum.lim"),
        "(#distributed-enum AppError ())
        (#gn error-case (name payload) `((#enum-contribute AppError (,name ,payload))))",
    )
    .unwrap();
    fs::write(
        root.join("first.lim"),
        "(#alias AppError = ./enum.lim::AppError) (#alias error-case = ./enum.lim::error-case) (#generate error-case @AppError.First #u64)",
    )
    .unwrap();
    fs::write(
        root.join("last.lim"),
        "(#alias AppError = ./enum.lim::AppError) (#alias error-case = ./enum.lim::error-case) (#generate error-case @AppError.Last #u32)",
    )
    .unwrap();
    for aliases in [
        "(#alias AppError.Last = ./last.lim::AppError.Last) (#alias AppError.First = ./first.lim::AppError.First)",
        "(#alias AppError.First = ./first.lim::AppError.First) (#alias AppError.Last = ./last.lim::AppError.Last)",
    ] {
        let source = format!(
            "(#alias AppError = ./enum.lim::AppError) {aliases} (#enum-contribute AppError (AppError.First #u64))
          (#fn main () #u64
            (#return (#match (AppError.First 42u64)
              (#case (AppError.First value) value)
              (#case (AppError.Last value) (#as value #u64)))))"
        );
        fs::write(root.join("main.lim"), &source).unwrap();
        for _ in 0..2 {
            let output = support::run(
                Command::new(env!("CARGO_BIN_EXE_lim"))
                    .arg(root.join("main.lim"))
                    .arg("-o")
                    .arg(root.join("program")),
                Duration::from_secs(30),
                1024 * 1024,
            )
            .unwrap();
            assert!(output.0.success(), "{}", String::from_utf8_lossy(&output.2));
            let run = support::run(
                &mut Command::new(root.join("program")),
                Duration::from_secs(2),
                1024,
            )
            .unwrap();
            assert_eq!(run.0.code(), Some(42));
        }
    }
}

#[test]
fn cfg_and_file_aliases_apply_before_merging() {
    let scratch = support::Scratch::new("distributed-enum-cfg");
    fs::write(
        scratch.path().join("errors.lim"),
        "(#distributed-enum Error ())
        (#enum-contribute Error (Error.Stable #u64))
        (#cfg-if (#cfg-is #extra yes) (#enum-contribute Error (Error.Extra #u32)))
        (#fn value () #u64 (#return (#match (Error.Stable 42u64)
          (#case (Error.Stable value) value) (#case _ 0u64))))",
    )
    .unwrap();
    for extra in ["no", "yes"] {
        let mut config = lim::CompileConfig::default();
        config.set("extra", extra);
        lim::compile_source_to_assembly(
            "(#alias value = ./errors.lim::value)
          (#fn main () #u64 (#return (#call value (:))))",
            &scratch.path().join("main.lim"),
            &config,
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
    }
}

#[test]
fn conflicts_and_unknown_targets_have_precise_diagnostics() {
    for (source, token, expected) in [
        ("(#enum-contribute missing (Missing.Case #u64))", "missing", "missing distributed enum"),
        ("(#distributed-enum Error ())\n(#enum-contribute Error (Error.Case #u64))\n(#enum-contribute Error (Error.Case #u32))", "(Error.Case #u32)", "conflicting definitions"),
        ("(#distributed-enum Error ()) (#distributed-enum Error ())", "Error", "duplicate distributed enum"),
    ] {
        let scratch = support::Scratch::new("distributed-enum-errors");
        let error = lim::compile_source_to_assembly(source, &scratch.path().join("input.lim"),
          &lim::CompileConfig::default(), &scratch.path().join("cache"),
          lim::TargetDescription::X86_64_SYSTEM_V).unwrap_err();
        assert!(error.message.contains(expected), "{error:?}");
        let span = error.span.expect("source-spanned distributed enum diagnostic");
        assert_eq!(&source[span.start..span.end], token);
        assert!(lim::render_diagnostic(&error, source, "input.lim").contains('^'));
    }
}

#[test]
fn linear_payloads_propagate_without_marking_the_distributed_enum() {
    let source = "(#struct Resource (#linear) (: value #u64))
        (#distributed-enum Error ())
        (#enum-contribute Error (Error.Failure Resource))
        (#fn main () ()
          (#let error Error (Error.Failure (#struct-literal Resource (: value 1u64))))
          (#return ()))";
    assert!(check(source).is_err());
    check(&source.replace("(#return ())", "(#forget error) (#return ())")).unwrap();
}

#[test]
fn general_distributed_syntax_is_no_longer_supported() {
    for source in [
        "(#syntax-collection Entries)",
        "(#syntax-contribute Entries key 42u64)",
        "(#syntax-distribute Entries)",
    ] {
        assert!(lim::parse_program(source).is_err(), "accepted {source}");
    }
}

#[test]
fn unprefixed_aliased_payloads_point_to_the_contributing_file() {
    let scratch = support::Scratch::new("distributed-enum-payload-span");
    fs::write(
        scratch.path().join("enum.lim"),
        "(#distributed-enum Error ())",
    )
    .unwrap();
    let contribution =
        "(#alias Error = ./enum.lim::Error) (#enum-contribute Error (Error.Failure u64))";
    fs::write(scratch.path().join("contribution.lim"), contribution).unwrap();
    let error = lim::compile_source_to_assembly(
        "(#alias Error = ./enum.lim::Error) (#alias Error.Failure = ./contribution.lim::Error.Failure)",
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("must use its '#' prefix"),
        "{error:?}"
    );
    assert!(
        error
            .source_name
            .as_deref()
            .unwrap()
            .ends_with("contribution.lim"),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(&contribution[span.start..span.end], "u64");
}
