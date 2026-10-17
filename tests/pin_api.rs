mod support;

use std::{fs, process::Command, time::Duration};

fn source() -> String {
    include_str!("../examples/stationary_pin.lim").replace(
        "../library/pin.lim",
        &format!("{}/library/pin.lim", env!("CARGO_MANIFEST_DIR")),
    )
}

fn compile(source: &str, scratch: &support::Scratch) -> Result<String, lim::Diagnostic> {
    lim::compile_source_with_generated_sources(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join(".lim/cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
        None,
        &scratch.path().join(".lim"),
    )
}

#[test]
fn scoped_pins_are_inspectable_and_cleanup_runs_before_return() {
    let scratch = support::Scratch::new("pin-api-scope");
    let source = source().replace(
        "(#fn destroy-frame (: pin PinnedFrame) ()",
        "(#fn destroy-frame (: pin PinnedFrame) ()
      (#let byte #u64 67u64)
      (#let pointer (#ptr #u64) (#unsafe (#addr-of byte)))
      (#let written #i64 (#unsafe (#linux-syscall #i64 1usize (1usize pointer 1usize))))
      (#assert (#i64.== written 1i64))",
    );
    let assembly = compile(&source, &scratch).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert_eq!(stdout, b"C", "cleanup must run exactly once");

    let generated = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "lim"))
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    for expected in [
        "(#opaque PinnedFrame)",
        "(#fn PinnedFrame::value::read",
        "(#fn PinnedFrame::value::write",
        "(#fn with-pinned-frame",
        "(#let-mut storage Frame value)",
        "(#call destroy-frame",
        "(#forget storage)",
    ] {
        assert!(generated.contains(expected), "missing {expected}");
    }
    assert!(!generated.contains("#let-pin"));
    assert!(!generated.contains("#pin-end"));
    // The same literal invocation reuses the same hashed artifacts.
    assert_eq!(compile(&source, &scratch).unwrap(), assembly);
}

#[test]
fn opaque_pins_cannot_be_unwrapped_forged_or_cloned_in_safe_code() {
    for (name, extra, expected) in [
        ("field", "(#fn bad (: pin PinnedFrame) () (#let raw (#pin-ref-mut Frame) (#get pin view)) (#forget raw) (#return ()))", "opaque"),
        ("pattern", "(#fn bad (: pin PinnedFrame) () (#let (PinnedFrame raw) PinnedFrame pin) (#forget raw) (#return ()))", "opaque"),
        ("forge", "(#fn bad (: view (#pin-ref-mut Frame)) PinnedFrame (#return (#struct-literal PinnedFrame (: view view))))", "opaque"),
        ("constructor", "(#fn bad (: view (#pin-ref-mut Frame)) PinnedFrame (#return (#unsafe-call PinnedFrame::from-mut (: view view))))", "unsafe"),
        ("unwrap", "(#fn bad (: pin PinnedFrame) (#pin-ref-mut Frame) (#return (#unsafe-call PinnedFrame::into-view (: pin pin))))", "unsafe"),
        ("clone", "(#fn bad (: pin PinnedFrame) () (#let duplicate PinnedFrame (#clone pin)) (#forget duplicate) (#forget pin) (#return ()))", "cloned"),
        ("nested-clone", "(#fn bad (: pin PinnedFrame) () (#let wrapped (#tuple PinnedFrame) (#tuple pin)) (#let duplicate (#tuple PinnedFrame) (#clone wrapped)) (#forget wrapped) (#forget duplicate) (#return ()))", "cloned"),
        ("private-storage", "(#fn bad (: pin PinnedFrame) () (#forget pin) (#forget storage) (#return ()))", "unknown"),
        ("generated-field", "(#gn steal () `((#fn bad (: pin PinnedFrame) () (#let raw (#pin-ref-mut Frame) (#get pin view)) (#forget raw) (#return ())))) (@steal)", "opaque"),
    ] {
        let scratch = support::Scratch::new(&format!("pin-api-{name}"));
        let error = compile(&format!("{}\n{extra}", source()), &scratch).unwrap_err();
        assert!(error.message.contains(expected), "{name}: {error:?}");
        let span = error.span.expect("offending expression must be underlined");
        if name == "generated-field" {
            assert_ne!(span.source_id, 0, "generated code must retain its exact span");
            assert!(!error.expansion_provenance.is_empty());
        } else {
            assert_eq!(span.source_id, 0, "{name}: {error:?}");
        }
        assert!(span.end > span.start, "{name}: empty underline");
    }
}

#[test]
fn scoped_pin_handles_cannot_escape_the_private_storage() {
    let scratch = support::Scratch::new("pin-api-escape");
    let source = source()
        .replace(": result #u64", ": result PinnedFrame")
        .replace("(#fn drive-frame (: pin PinnedFrame) #u64", "(#fn drive-frame (: pin PinnedFrame) PinnedFrame")
        .replace("  (#forget handle)\n  (#return result)", "  (#return handle)")
        .replace("(#return (#call with-pinned-frame\n    (: value (#struct-literal Frame (: value 0u64)))))", "(#let escaped PinnedFrame (#call with-pinned-frame (: value (#struct-literal Frame (: value 0u64)))))\n  (#forget escaped) (#return 0u64)");
    let error = compile(&source, &scratch).unwrap_err();
    assert!(
        error.message.contains("borrow") || error.message.contains("reference"),
        "{error:?}"
    );
    assert!(error.span.is_some());
}

#[test]
fn pin_generator_arguments_and_copy_proof_are_checked() {
    for (arguments, expected) in [
        (
            "(: name PinnedFrame : type Frame : fields (: value #u64))",
            "",
        ),
        (
            "(: type Frame : name PinnedFrame : fields (: value #bool))",
            "expected Bool",
        ),
        (
            "(: type Frame : name PinnedFrame : copy true : fields (: value #u64))",
            "linear",
        ),
        (
            "(: type Frame : name PinnedFrame : fields (: value #u64) : typo true)",
            "unknown named",
        ),
        (
            "(: type Frame : name PinnedFrame : name Other)",
            "repeats key",
        ),
        ("(: type Frame)", "missing key"),
        (
            "(: type Frame : name PinnedFrame : copy 1)",
            "true or false",
        ),
    ] {
        let scratch = support::Scratch::new("pin-api-arguments");
        let changed = source().replace(
            "(: type Frame : name PinnedFrame : fields (: value #u64))",
            arguments,
        );
        let result = compile(&changed, &scratch);
        if expected.is_empty() {
            result.unwrap();
        } else {
            let error = result.unwrap_err();
            assert!(error.message.contains(expected), "{arguments}: {error:?}");
            assert!(error.span.is_some());
        }
    }
}

#[test]
fn whole_value_copy_access_rejects_exclusive_reference_fields() {
    let scratch = support::Scratch::new("pin-api-copy-exclusive");
    let source = format!(
        "{}
      (#struct Held () (: reference (#ref-mut #u64)))
      (@#pin (: type Held : name PinnedHeld : copy true))",
        source()
    );
    assert!(
        compile(&source, &scratch).is_err(),
        "a mutable reference-bearing value must not pass the generated Copy proof"
    );
}

fn projection_source() -> String {
    format!(
        "(#import \"{}/library/pin.lim\")
      (#struct Inner (#linear) (: value #u64))
      (#struct Outer (#linear) (: child Inner))
      (@#pin (: type Inner : name PinnedInner : fields (: value #u64)))
      (@#pin (: type Outer : name PinnedOuter : projections (: child PinnedInner)))
      (@#pin-scope (: type Outer : pin PinnedOuter : name with-outer
        : run drive-outer : destroy destroy-outer : result #u64))
      (#fn drive-outer (: pin PinnedOuter) #u64
        (#let-mut handle PinnedOuter pin)
        (#let-mut child PinnedInner (#call PinnedOuter::child::project-mut (: pin handle)))
        (#call PinnedInner::value::write (: pin (#borrow-mut child) : value 42u64))
        (#let result #u64 (#call PinnedInner::value::read (: pin (#borrow child))))
        (#forget child) (#return result))
      (#fn destroy-outer (: pin PinnedOuter) () (#forget pin) (#return ()))
      (#fn main () #u64 (#return (#call with-outer
        (: value (#struct-literal Outer (: child (#struct-literal Inner (: value 0u64))))))))",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[test]
fn pinned_linear_fields_are_projected_without_moving_them() {
    let scratch = support::Scratch::new("pin-api-projection");
    let assembly = compile(&projection_source(), &scratch).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}

#[test]
fn projected_handles_cannot_escape_or_overlap_exclusively() {
    let source = projection_source();
    let overlapping = source.replace(
        "(#call PinnedInner::value::write",
        "(#let duplicate PinnedInner (#call PinnedOuter::child::project-mut (: pin handle))) (#forget duplicate)\n        (#call PinnedInner::value::write");
    let escaping = source
        .replace(": result #u64", ": result PinnedInner")
        .replace("(#fn drive-outer (: pin PinnedOuter) #u64", "(#fn drive-outer (: pin PinnedOuter) PinnedInner")
        .replace("(#forget child) (#return result)", "(#return child)")
        .replace("(#fn main () #u64 (#return (#call with-outer\n        (: value (#struct-literal Outer (: child (#struct-literal Inner (: value 0u64))))))))", "(#fn main () #u64 (#let escaped PinnedInner (#call with-outer (: value (#struct-literal Outer (: child (#struct-literal Inner (: value 0u64))))))) (#forget escaped) (#return 0u64))");
    for source in [overlapping, escaping] {
        let scratch = support::Scratch::new("pin-api-projection-invalid");
        let error = compile(&source, &scratch).unwrap_err();
        assert!(
            error.message.contains("borrow")
                || error.message.contains("reference")
                || error.message.contains("consumed")
                || error.message.contains("moved")
                || error.message.contains("used more than once"),
            "{error:?}"
        );
        assert!(error.span.is_some());
    }
}
