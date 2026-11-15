mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

const SOURCE: &str = "
#struct Pair () ((left #u64) (right #u64))
#enum Slot () ((Slot.Empty) (Slot.Full Pair))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let-mut slot Slot (Slot.Full (#struct-literal Pair ((left 39u64) (right 2u64)))))
    (#let pinned (#pin-ref-mut Slot) (#pin-borrow-mut slot))
    (#let payload (#pin-ref-mut Pair)
      (#unsafe (#pin-get-payload-unchecked-mut pinned Slot.Full)))
    (#pin-set-field payload left 40u64)
    (#let answer #u64 (#u64::add-wrap (#get payload left) (#get payload right)))
    (#forget payload)
    (#forget pinned)
    (#forget slot)
    (#return answer)\n  );\n}\n";

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("unchecked-payload");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn unchecked_projection_preserves_stack_layout_without_a_tag_guard() {
    run_without_tag_guard(SOURCE);
}

fn run_without_tag_guard(source: &str) {
    let assembly = compile(source).unwrap();
    assert!(!assembly.contains("inactive_pinned_enum_payload_borrow"));
    let scratch = support::Scratch::new("unchecked-payload-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        &mut std::process::Command::new(binary),
        std::time::Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

#[test]
fn unchecked_projection_preserves_heap_layout_without_a_tag_guard() {
    let source = SOURCE
        .replace(
            "(#let-mut slot Slot (Slot.Full (#struct-literal Pair ((left 39u64) (right 2u64)))))",
            "(#let pointer (#ptr-mut Slot) (#unsafe (#linux-syscall (#ptr-mut Slot) 9usize
            (0usize (#size-of Slot) 3usize 34usize -1i64 0usize))))
         (#let-mut slot (#pin-own Slot) (#unsafe (#pin-own-of pointer
            (Slot.Full (#struct-literal Pair ((left 39u64) (right 2u64)))))))",
        )
        .replace("(#pin-borrow-mut slot)", "(#pin-own-borrow-mut slot)")
        .replace(
            "(#forget slot)",
            "(#let raw (#ptr-mut Slot) (#unsafe (#pin-release slot)))
         (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (raw (#size-of Slot)))) 0i64))",
        );
    run_without_tag_guard(&source);
}

#[test]
fn unchecked_projection_requires_unsafe_and_preserves_alias_rules() {
    let unsafe_missing = SOURCE.replace(
        "(#unsafe (#pin-get-payload-unchecked-mut pinned Slot.Full))",
        "(#pin-get-payload-unchecked-mut pinned Slot.Full)",
    );
    let diagnostic = compile(&unsafe_missing).unwrap_err();
    assert_eq!(diagnostic.code, DiagnosticCode::Unsafe);
    let span = diagnostic.span.unwrap();
    assert_eq!(
        &unsafe_missing[span.start..span.end],
        "#pin-get-payload-unchecked-mut"
    );

    let conflict = SOURCE.replace(
        "(#pin-set-field payload left 40u64)",
        "(#let duplicate (#pin-ref Pair) (#unsafe (#pin-get-payload-unchecked pinned Slot.Full))) (#forget duplicate) (#pin-set-field payload left 40u64)",
    );
    assert_eq!(compile(&conflict).unwrap_err().code, DiagnosticCode::Borrow);

    for removed in ["#pin-get-payload", "#pin-get-payload-mut"] {
        let checked = SOURCE.replace(
            "(#unsafe (#pin-get-payload-unchecked-mut pinned Slot.Full))",
            &format!("({removed} pinned Slot.Full)"),
        );
        assert!(
            compile(&checked).is_err(),
            "asserting projection must not remain callable"
        );
    }

    let indexed = SOURCE.replace(
        "(#pin-get-payload-unchecked-mut pinned Slot.Full)",
        "(#pin-get-payload-unchecked-mut pinned Slot.Full 0)",
    );
    assert!(
        compile(&indexed).is_err(),
        "indexed pin payload syntax must be rejected"
    );
}

#[test]
fn unchecked_projection_still_checks_payload_types_and_lifetimes() {
    for (from, to, message) in [
        ("pinned Slot.Full", "pinned missing", "variant 'missing'"),
        (
            "(#pin-ref-mut Slot) (#pin-borrow-mut slot)",
            "(#pin-ref Slot) (#pin-borrow slot)",
            "mutable pinned enum reference",
        ),
    ] {
        let diagnostic = compile(&SOURCE.replace(from, to)).unwrap_err();
        assert!(diagnostic.message.contains(message), "{diagnostic:?}");
        assert!(diagnostic.span.is_some(), "{diagnostic:?}");
    }
    let source = "#struct Pair () ((left #u64) (right #u64))
#enum Slot () ((Slot.Empty) (Slot.Full Pair))
#fn bad {
  #params = ();
  #returns = (#pin-ref Pair);
  #body = (
          (#let-mut slot Slot (Slot.Full (#struct-literal Pair ((left 1u64) (right 2u64)))))
          (#let pinned (#pin-ref Slot) (#pin-borrow slot))
          (#return (#unsafe (#pin-get-payload-unchecked pinned Slot.Full)))\n  );\n}\n";
    let diagnostic = compile(source).unwrap_err();
    assert_eq!(diagnostic.code, DiagnosticCode::Borrow, "{diagnostic:?}");
    assert!(diagnostic.span.is_some());
}
