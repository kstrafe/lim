mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("word-storage");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str) {
    let assembly = compile(source).unwrap();
    let scratch = support::Scratch::new("word-storage-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        &mut std::process::Command::new(binary),
        std::time::Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

const SOURCE: &str = "
(#struct Pair (: left #u8 : right #u64))
(#fn inspect (: pair (#ref Pair)) #u64
  (#return (#u64.+.wrap (#as (#get pair left) #u64) (#get pair right))))
(#fn main () #u64
  (#let-mut words (#array #u64 2) (#array-repeat 0u64))
  (#unsafe (#word-write Pair (#borrow-slice-mut words)
    (#struct-literal Pair (: left 40u8 : right 2u64))))
  (#let view (#ref Pair) (#unsafe (#word-view (#ref Pair) (#borrow-slice words))))
  (#let result #u64 (#call inspect (: pair view)))
  (#forget view) (#return result))";

#[test]
fn flat_word_views_preserve_stack_layout() {
    run(SOURCE);
}

#[test]
fn word_access_checks_unsafe_types_aliases_and_lifetimes() {
    let missing = SOURCE.replace(
        "(#unsafe (#word-view (#ref Pair) (#borrow-slice words)))",
        "(#word-view (#ref Pair) (#borrow-slice words))",
    );
    let error = compile(&missing).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Unsafe, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&missing[span.start..span.end], "#word-view");
    let overlap = SOURCE.replace(
        "(#let result",
        "(#set-index words 0usize 99u64) (#let result",
    );
    assert_eq!(compile(&overlap).unwrap_err().code, DiagnosticCode::Borrow);
    let escaping = "(#fn bad () (#ref #u64)
      (#let words (#array #u64 1) (#array-of (#array #u64 1) 42u64))
      (#return (#unsafe (#word-view (#ref #u64) (#borrow-slice words)))))";
    assert_eq!(compile(escaping).unwrap_err().code, DiagnosticCode::Borrow);
    let shared = SOURCE
        .replace("#word-view (#ref Pair)", "#word-view (#ref-mut Pair)")
        .replace("(#let view (#ref Pair)", "(#let view (#ref-mut Pair)");
    assert_eq!(compile(&shared).unwrap_err().code, DiagnosticCode::Borrow);
    let incorrect_value = SOURCE.replace("left 40u8", "left 40u64");
    assert_eq!(
        compile(&incorrect_value).unwrap_err().code,
        DiagnosticCode::Type
    );
    let incorrect_storage = SOURCE
        .replace("(#array #u64 2)", "(#array #u8 2)")
        .replace("(#array-repeat 0u64)", "(#array-repeat 0u8)");
    assert_eq!(
        compile(&incorrect_storage).unwrap_err().code,
        DiagnosticCode::Type
    );
}

#[test]
fn word_reads_and_writes_handle_large_aggregates() {
    run("(#fn main () #u64
      (#let-mut words (#array #u64 8) (#array-repeat 0u64))
      (#unsafe (#word-write (#array #u64 8) (#borrow-slice-mut words)
        (#array-of (#array #u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 42u64)))
      (#let value (#array #u64 8) (#unsafe (#word-read (#array #u64 8) (#borrow-slice words))))
      (#return (#index value 7usize)))");
}

#[test]
fn heap_word_views_preserve_flat_not_packed_layout() {
    let source = SOURCE.replace(
        "(#let-mut words (#array #u64 2) (#array-repeat 0u64))",
        "(#let pointer (#ptr-mut (#array #u64 2))
          (#unsafe (#linux-syscall (#ptr-mut (#array #u64 2)) 9usize
            (0usize 16usize 3usize 34usize -1i64 0usize))))
         (#let-mut owner (#pin-own (#array #u64 2))
          (#unsafe (#pin-own-of pointer (#array-of (#array #u64 2) 0u64 0u64))))",
    );
    let source = source.replace("(#unsafe (#word-write", "(#let writable (#pin-ref-mut (#array #u64 2)) (#pin-own-borrow-mut owner))\n  (#unsafe (#word-write")
        .replace("(#borrow-slice-mut words)", "(#slice-mut-of (#unsafe (#ptr-borrow-mut writable (#ref-ptr writable))))")
        .replace("(#let view", "(#forget writable)\n  (#let readable (#pin-ref (#array #u64 2)) (#pin-own-borrow owner))\n  (#let view")
        .replace("(#borrow-slice words)", "(#slice-of (#unsafe (#ptr-borrow readable (#ref-ptr readable))))")
        .replace("(#forget view) (#return result)",
          "(#forget view) (#forget readable)
           (#let raw (#ptr-mut (#array #u64 2)) (#unsafe (#pin-release owner)))
           (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (raw 16usize))) 0i64))
           (#return result)");
    run(&source);
    let invalid = source.replace("(#forget view) ", "");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn disjoint_word_ranges_keep_a_sibling_address_live() {
    let source = "(#fn main () #u64
      (#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 40u64 0u64))
      (#let kept (#ref #u64) (#unsafe (#word-view (#ref #u64) (#borrow-slice words 0usize 1usize))))
      (#unsafe (#word-write #u64 (#borrow-slice-mut words 1usize 2usize) 2u64))
      (#let other #u64 (#unsafe (#word-read #u64 (#borrow-slice words 1usize 2usize))))
      (#let result #u64 (#u64.+.wrap (#deref kept) other))
      (#forget kept) (#return result))";
    run(source);
    let invalid = source.replace(
        "#borrow-slice-mut words 1usize 2usize",
        "#borrow-slice-mut words 0usize 1usize",
    );
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn returned_views_retain_their_callers_storage_lifetime() {
    let source = "(#fn view (: words (#slice #u64)) (#ref #u64)
      (#return (#unsafe (#word-view (#ref #u64) words))))
    (#fn main () #u64
      (#let-mut words (#array #u64 1) (#array-of (#array #u64 1) 42u64))
      (#let selected (#ref #u64) (#call view (: words (#borrow-slice words))))
      (#let result #u64 (#deref selected)) (#forget selected) (#return result))";
    run(source);
    let invalid = source.replace(
        "(#let result",
        "(#set-index words 0usize 99u64) (#let result",
    );
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn numeric_words_cannot_invent_reference_provenance() {
    let source = "(#struct Holder (: item (#ref #u64)))
      (#fn bad (: words (#slice #u64)) (#ref #u64)
        (#let holder (#ref Holder) (#unsafe (#word-view (#ref Holder) words)))
        (#return (#get holder item)))";
    let error = compile(source).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing slot provenance"),
        "{error:?}"
    );
}

#[test]
fn scalar_float_wide_and_pinned_views_use_the_same_word_layout() {
    for (ty, value, read) in [
        ("#i8", "42i8", "(#as (#deref view) #u64)"),
        ("#u128", "42u128", "(#as (#deref view) #u64)"),
        ("#f32", "42.0f32", "(#as (#deref view) #u64)"),
        ("#f64", "42.0f64", "(#as (#deref view) #u64)"),
    ] {
        run(&format!(
            "(#fn main () #u64
          (#let-mut words (#array #u64 2) (#array-repeat 0u64))
          (#unsafe (#word-write {ty} (#borrow-slice-mut words) {value}))
          (#let view (#pin-ref {ty}) (#unsafe (#word-view (#pin-ref {ty}) (#borrow-slice words))))
          (#let result #u64 {read}) (#forget view) (#return result))"
        ));
    }
}

#[test]
fn contiguous_partial_ownership_restoration_keeps_the_whole_address() {
    run("(#struct Token (: value #u64)) (#linear Token)
      (#struct Owner (: kept #u64 : item Token))
      (#fn inspect (: owner (#ref Owner)) #u64
        (#return (#u64.+.wrap (#get owner kept) (#get (#get owner item) value))))
      (#fn main () #u64
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Owner (#borrow-slice-mut words)
          (#struct-literal Owner (: kept 40u64 : item (#struct-literal Token (: value 1u64))))))
        (#let kept (#ref #u64)
          (#unsafe (#word-view (#ref #u64) (#borrow-slice words 0usize 1usize))))
        (#let moved Token (#unsafe (#word-read Token (#borrow-slice words 1usize 2usize))))
        (#forget moved)
        (#unsafe (#word-write Token (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Token (: value 2u64))))
        (#let whole (#ref Owner) (#unsafe (#word-view (#ref Owner) (#borrow-slice words))))
        (#let selected (#ref #u64) (#borrow (#get whole kept)))
        (#assert (#usize.== (#ptr-address (#ref-ptr kept)) (#ptr-address (#ref-ptr selected))))
        (#let answer #u64 (#call inspect (: owner whole)))
        (#forget selected) (#forget whole) (#forget kept)
        (#let remaining Owner (#unsafe (#word-read Owner (#borrow-slice words))))
        (#forget remaining) (#return answer))");
}
