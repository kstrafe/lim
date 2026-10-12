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

const REFERENCE_WORDS: &str = "
(#struct Pair (: left #u8 : right #u64))
(#fn expose (: value (#pin-ref-mut Pair)) (#slice-mut #u64)
  (#return (#unsafe (#word-view (#slice-mut #u64) value))))
(#fn main () #u64
  (#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 40u64 2u64))
  (#let target (#pin-ref-mut Pair)
    (#unsafe (#word-view (#pin-ref-mut Pair) (#borrow-slice-mut words))))
  (#let raw (#slice-mut #u64) (#call expose (: value target)))
  (#assert (#usize.== (#slice-mut-len raw) 2usize))
  (#unsafe (#word-write Pair raw (#struct-literal Pair (: left 20u8 : right 22u64))))
  (#let raw-read (#slice #u64) (#unsafe (#word-view (#slice #u64) target)))
  (#let result Pair (#unsafe (#word-read Pair raw-read)))
  (#forget raw-read) (#forget target)
  (#let answer #u64 (#u64.+.wrap (#as (#get result left) #u64) (#get result right)))
  (#forget result) (#return answer))";

#[test]
fn reference_word_views_preserve_selected_stack_layout_and_helper_lifetimes() {
    run(REFERENCE_WORDS);
    let conflict = REFERENCE_WORDS.replace(
        "(#let result Pair",
        "(#set-index words 0usize 99u64) (#let result Pair",
    );
    assert_eq!(compile(&conflict).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn reference_word_views_preserve_heap_layout_and_owner_lifetimes() {
    let source = REFERENCE_WORDS
        .replace(
            "(#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 40u64 2u64))",
            "(#let pointer (#ptr-mut (#array #u64 2))
          (#unsafe (#linux-syscall (#ptr-mut (#array #u64 2)) 9usize
            (0usize 16usize 3usize 34usize -1i64 0usize))))
         (#let-mut owner (#pin-own (#array #u64 2))
          (#unsafe (#pin-own-of pointer (#array-of (#array #u64 2) 40u64 2u64))))",
        )
        .replace(
            "(#borrow-slice-mut words)",
            "(#unsafe (#word-view (#slice-mut #u64) (#pin-own-borrow-mut owner)))",
        )
        .replace(
            "(#forget raw-read) (#forget target)",
            "(#forget raw-read) (#forget target)
         (#let pointer-out (#ptr-mut (#array #u64 2)) (#unsafe (#pin-release owner)))
         (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (pointer-out 16usize))) 0i64))",
        );
    run(&source);
    let invalid = source.replace("(#forget raw-read) (#forget target)", "");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn reference_word_views_check_unsafe_mutability_types_and_escapes() {
    let missing = REFERENCE_WORDS.replace(
        "(#unsafe (#word-view (#slice-mut #u64) value))",
        "(#word-view (#slice-mut #u64) value)",
    );
    assert_eq!(compile(&missing).unwrap_err().code, DiagnosticCode::Unsafe);
    let immutable = REFERENCE_WORDS.replace("(#pin-ref-mut Pair)", "(#pin-ref Pair)");
    assert_eq!(
        compile(&immutable).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let wrong_element = REFERENCE_WORDS.replace("(#slice-mut #u64)", "(#slice-mut #u8)");
    assert_eq!(
        compile(&wrong_element).unwrap_err().code,
        DiagnosticCode::Type
    );
    let escape = "(#fn bad () (#slice #u64)
      (#let value #u64 42u64)
      (#return (#unsafe (#word-view (#slice #u64) (#borrow value)))))";
    assert_eq!(compile(escape).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn word_staging_preserves_observable_clone_hooks() {
    let source = "(#struct Value (: number #u64 : count (#ptr-mut #u64)))
      (#fn Value-clone (: value Value) Value
        (#unsafe (#ptr-write (#get value count)
          (#u64.+.wrap (#ptr-read (#get value count)) 1u64))) (#return value))
      (#fn main () #u64
        (#let-mut count #u64 0u64)
        (#let pointer (#ptr-mut #u64) (#ref-ptr (#borrow-mut count)))
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#let initial Value (#struct-literal Value (: number 40u64 : count pointer)))
        (#unsafe (#word-write Value (#borrow-slice-mut words) initial))
        (#let source Value (#unsafe (#word-read Value (#borrow-slice words))))
        (#let copied Value (#block (#let nested Value source) (#clone nested)))
        (#unsafe (#word-write Value (#borrow-slice-mut words)
          (#block (#let staged Value copied) (#clone staged))))
        (#assert (#u64.== count 2u64))
        (#let result Value (#unsafe (#word-read Value (#borrow-slice words))))
        (#return (#u64.+.wrap (#get result number) count)))";
    run(source);
    let large = source
        .replace(
            "(: number #u64 : count (#ptr-mut #u64))",
            "(: number #u64 : count (#ptr-mut #u64)
              : a #u64 : b #u64 : c #u64 : d #u64 : e #u64)",
        )
        .replace("(#array #u64 2)", "(#array #u64 7)")
        .replace(
            "(: number 40u64 : count pointer)",
            "(: number 40u64 : count pointer
              : a 1u64 : b 2u64 : c 3u64 : d 4u64 : e 5u64)",
        );
    run(&large);
}

#[test]
fn zero_word_markers_do_not_exhaust_native_return_registers() {
    run("(#struct Marked (: number #u64
        : a (#array #u64 0) : b (#array #u64 0) : c (#array #u64 0)
        : d (#array #u64 0) : e (#array #u64 0) : f (#array #u64 0)))
      (#fn make () Marked
        (#return (#struct-literal Marked (: number 42u64
          : a (#array-of (#array #u64 0)) : b (#array-of (#array #u64 0))
          : c (#array-of (#array #u64 0)) : d (#array-of (#array #u64 0))
          : e (#array-of (#array #u64 0)) : f (#array-of (#array #u64 0))))))
      (#fn main () #u64 (#let value Marked (#call make ()))
        (#return (#get value number)))");
}

#[test]
fn typed_reference_holder_lends_its_word_view_without_duplicating_the_loan() {
    let source = "(#struct Holder (: view (#ref-mut #u64)))
      (#fn touch (: target (#ref-mut #u64)) ()
        (#deref-set target (#u64.+.wrap (#deref target) 1u64)) (#return ()))
      (#fn main () #u64
        (#let-mut words (#array #u64 1) (#array-of (#array #u64 1) 40u64))
        (#let view (#ref-mut #u64) (#unsafe (#word-view (#ref-mut #u64)
          (#block
            (#let anchor (#ref-mut (#array #u64 1)) (#borrow-mut words))
            (#borrow-slice-mut (#deref anchor))))))
        (#let-mut holder Holder (#struct-literal Holder (: view view)))
        (#call touch (: target (#deref (#borrow-mut (#get holder view)))))
        (#call touch (: target (#deref (#borrow-mut (#get holder view)))))
        (#let result #u64 (#deref (#get holder view)))
        (#forget holder) (#return result))";
    run(source);
    let through_owner = source
        .replace(
            "(#let-mut holder Holder (#struct-literal Holder (: view view)))",
            "(#let-mut holder Holder (#struct-literal Holder (: view view)))
           (#let owner-view (#ref-mut Holder) (#borrow-mut holder))",
        )
        .replace("(#get holder view)", "(#get owner-view view)")
        .replace("(#forget holder)", "(#forget owner-view) (#forget holder)");
    run(&through_owner);
    let conflict = through_owner
        .replacen(
            "(#call touch",
            "
      (#let child (#ref #u64) (#borrow (#deref (#get owner-view view))))
      (#call touch",
            1,
        )
        .replace(
            "(#forget owner-view)",
            "(#forget child) (#forget owner-view)",
        );
    let error = compile(&conflict).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Borrow, "{}", error.message);
}

#[test]
fn word_view_outlives_temporary_anchor_but_not_its_parameter() {
    let source = "(#fn read (: words (#ref-mut (#array #u64 2))) #u64
      (#let selected (#ref #u64) (#unsafe (#word-view (#ref #u64)
        (#block
          (#let anchor (#ref (#array #u64 2)) (#borrow (#deref words)))
          (#borrow-slice (#deref anchor) 0usize 1usize)))))
      (#let again (#ref #u64) selected)
      (#return (#u64.+.wrap (#deref selected) (#deref again))))
      (#fn main () #u64
        (#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 21u64 0u64))
        (#return (#call read (: words (#borrow-mut words)))))";
    run(source);
    let conflict = source.replace(
        "(#let again",
        "(#deref-set words (#array-of (#array #u64 2) 99u64 0u64)) (#let again",
    );
    assert_eq!(compile(&conflict).unwrap_err().code, DiagnosticCode::Borrow);
    let exclusive = source
        .replace(
            "(#let selected (#ref #u64)",
            "(#let selected (#ref-mut #u64)",
        )
        .replacen("#word-view (#ref #u64)", "#word-view (#ref-mut #u64)", 1)
        .replace(
            "(#let anchor (#ref (#array #u64 2)) (#borrow (#deref words)))",
            "(#let anchor (#ref-mut (#array #u64 2)) (#borrow-mut (#deref words)))",
        )
        .replace(
            "(#borrow-slice (#deref anchor)",
            "(#borrow-slice-mut (#deref anchor)",
        )
        .replace(
            "(#let again (#ref #u64) selected)",
            "(#let again (#ref #u64) (#borrow (#index (#deref words) 0usize)))",
        );
    assert_eq!(
        compile(&exclusive).unwrap_err().code,
        DiagnosticCode::Borrow
    );
}

#[test]
fn word_view_uses_result_mutability_without_losing_alias_protection() {
    let shared = SOURCE
        .replace("(#borrow-slice words)", "(#borrow-slice-mut words)")
        .replace(
            "(#let result",
            "(#let observed #u64 (#index words 0usize)) (#let result",
        );
    run(&shared);
    let conflicting_write = shared.replace(
        "(#let observed",
        "(#set-index words 0usize 99u64) (#let observed",
    );
    assert_eq!(
        compile(&conflicting_write).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let exclusive = shared
        .replace("(#let view (#ref Pair)", "(#let view (#ref-mut Pair)")
        .replace("#word-view (#ref Pair)", "#word-view (#ref-mut Pair)")
        .replace("(: pair (#ref Pair))", "(: pair (#ref-mut Pair))");
    assert_eq!(
        compile(&exclusive).unwrap_err().code,
        DiagnosticCode::Borrow
    );
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
        (#return (#get holder item)))
      (#fn main () #u64
        (#let words (#array #u64 1) (#array-of (#array #u64 1) 42u64))
        (#return (#deref (#call bad (: words (#borrow-slice words))))))";
    let error = compile(source).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing slot provenance")
            || error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn typed_word_writes_preserve_contained_reference_provenance() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder (: value (#borrow seed)))))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let result #u64 (#deref (#get copied value)))
        (#forget copied) (#forget words) (#set seed 0u64)
        (#return result))";
    run(source);
    run(&source.replace(
        "copied Holder (#unsafe (#word-read Holder",
        "copied (#ref Holder) (#unsafe (#word-view (#ref Holder)",
    ));
    let heap = source
        .replace("(#let-mut words (#array #u64 1) (#array-repeat 0u64))",
          "(#let allocation (#ptr-mut (#array #u64 1)) (#unsafe (#linux-syscall (#ptr-mut (#array #u64 1))
            9usize (0usize 8usize 3usize 34usize -1i64 0usize))))
           (#let-mut owner (#pin-own (#array #u64 1)) (#unsafe (#pin-own-of allocation (#array-repeat 0u64))))
           (#let anchor (#pin-ref-mut (#array #u64 1)) (#pin-own-borrow-mut owner))
           (#let writable (#ref-mut (#array #u64 1)) (#unsafe (#ptr-borrow-mut anchor (#ref-ptr anchor))))")
        .replace("#borrow-slice-mut words", "#borrow-slice-mut (#deref writable)")
        .replace("#borrow-slice words", "#borrow-slice (#deref writable)")
        .replace("(#forget words)", "(#forget writable) (#forget anchor)
          (#let released (#ptr-mut (#array #u64 1)) (#unsafe (#pin-release owner)))
          (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (released 8usize))) 0i64))");
    run(&heap);
    let invalid = source.replace("(#let result", "(#set seed 0u64) (#let result");
    let error = compile(&invalid).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn typed_word_reference_slots_use_real_flat_offsets() {
    let source = "(#struct Holder (: prefix #u128 : value (#ref #u64) : suffix #u64))
      (#fn main () #u64
        (#let-mut seed #u64 40u64)
        (#let-mut words (#array #u64 6) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 5usize)
          (#struct-literal Holder (: prefix 0u128 : value (#borrow seed) : suffix 2u64))))
        (#let view (#ref Holder) (#unsafe (#word-view (#ref Holder) (#borrow-slice words 1usize 5usize))))
        (#let result #u64 (#u64.+.wrap (#deref (#get view value)) (#get view suffix)))
        (#forget view) (#forget words) (#set seed 0u64) (#return result))";
    run(source);
    let invalid = source.replace(
        "#borrow-slice words 1usize 5usize",
        "#borrow-slice words 0usize 4usize",
    );
    assert!(
        compile(&invalid).is_err(),
        "a neighboring range cannot supply this slot's provenance"
    );
}

#[test]
fn owned_nested_word_slots_preserve_tuple_and_array_reference_origins() {
    let source = "(#struct Holder (: prefix #u128 : nested (#tuple #u64 (#array (#ref #u64) 2))))
      (#linear Holder)
      (#fn main () #u64
        (#let-mut left #u64 20u64) (#let-mut right #u64 22u64)
        (#let-mut words (#array #u64 5) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder (: prefix 0u128
            : nested (#tuple (#tuple #u64 (#array (#ref #u64) 2)) 0u64
              (#array-of (#array (#ref #u64) 2) (#borrow left) (#borrow right)))))))
        (#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let refs (#array (#ref #u64) 2) (#get (#get restored nested) 1))
        (#let answer #u64 (#u64.+.wrap (#deref (#index refs 0usize)) (#deref (#index refs 1usize))))
        (#forget refs) (#forget restored) (#forget words)
        (#set left 0u64) (#set right 0u64) (#return answer))";
    run(source);
    for name in ["left", "right"] {
        let invalid = source.replace("(#let answer", &format!("(#set {name} 0u64) (#let answer"));
        assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
    }
}

#[test]
fn numeric_overwrites_retire_typed_word_reference_provenance() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder (: value (#borrow seed)))))
        (#unsafe (#word-write #u64 (#borrow-slice-mut words) 0u64))
        (#set seed 42u64) (#return seed))";
    run(source);
    let invalid = source.replace("(#set seed 42u64)",
        "(#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words)))) (#forget restored) (#set seed 42u64)");
    let error = compile(&invalid).unwrap_err();
    assert!(
        error.message.contains("missing slot provenance"),
        "{error:?}"
    );
}

#[test]
fn exclusive_word_reads_require_an_exclusive_source_and_keep_aliases_checked() {
    let source = "(#struct Holder (: value (#ref-mut #u64)))
      (#fn write (: value (#ref-mut #u64)) () (#deref-set value 42u64) (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder (: value (#borrow-mut seed)))))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice-mut words))))
        (#call write (: value (#get copied value)))
        (#forget copied) (#forget words) (#return seed))";
    run(source);
    for invalid in [
        source.replace(
            "#word-read Holder (#borrow-slice-mut words)",
            "#word-read Holder (#borrow-slice words)",
        ),
        source.replace(
            "(#call write",
            "(#let alias (#ref #u64) (#borrow seed)) (#call write",
        ),
    ] {
        assert!(
            compile(&invalid).is_err(),
            "exclusive word storage must retain permission and alias checks"
        );
    }
}

#[test]
fn typed_word_writes_cannot_export_short_lived_references() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn bad (: words (#slice-mut #u64)) ()
        (#let local #u64 42u64)
        (#unsafe (#word-write Holder words
          (#struct-literal Holder (: value (#borrow local)))))
        (#return ()))";
    let error = compile(source).expect_err("caller word memory must not retain a local reference");
    assert!(
        matches!(error.code, DiagnosticCode::Borrow | DiagnosticCode::Linear),
        "{error:?}"
    );
}

#[test]
fn typed_word_reference_writes_require_resolved_slot_addresses() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn store (: words (#slice-mut #u64) : offset #usize : source (#ref #u64)) ()
        (#unsafe (#word-write Holder (#slice-mut-range words offset 2usize)
          (#struct-literal Holder (: value source))))
        (#return ()))";
    let error = compile(source).expect_err("unknown coordinates cannot establish typed slots");
    assert!(
        error.message.contains("unresolved slot address"),
        "{error:?}"
    );
}

#[test]
fn typed_word_writer_helpers_export_real_source_loans() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn store (: words (#slice-mut #u64) : source (#ref #u64)) ()
        (#unsafe (#word-write Holder words (#struct-literal Holder (: value source))))
        (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#call store (: words (#borrow-slice-mut words) : source (#borrow seed)))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let result #u64 (#deref (#get copied value)))
        (#forget copied) (#forget words) (#set seed 0u64) (#return result))";
    run(source);
    run(&source
        .replace("(#array #u64 1)", "(#array #u64 2)")
        .replace(
            "#borrow-slice-mut words)",
            "#borrow-slice-mut words 1usize 2usize)",
        )
        .replace("#borrow-slice words)", "#borrow-slice words 1usize 2usize)"));
    let invalid = source.replace("(#let result", "(#set seed 0u64) (#let result");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn typed_word_reader_helpers_require_actual_reference_inputs() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn read (: words (#slice #u64)) #u64
        (#let restored Holder (#unsafe (#word-read Holder words)))
        (#let answer #u64 (#deref (#get restored value)))
        (#forget restored) (#return answer))
      (#fn forward (: words (#slice #u64)) #u64
        (#return (#call read (: words words))))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Holder (: value (#borrow seed)))))
        (#let answer #u64 (#call forward (: words (#borrow-slice words 1usize 2usize))))
        (#forget words) (#set seed 0u64) (#return answer))";
    run(source);
    let invalid = source.replace(
        "(#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)\n          (#struct-literal Holder (: value (#borrow seed)))))", "");
    assert_ne!(source, invalid);
    let error =
        compile(&invalid).expect_err("a scalar return must not hide a forged reference read");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn documented_word_reader_contract_example_runs_natively() {
    let documentation = include_str!("../docs/language.md");
    let section = documentation
        .split("### Typed word-memory loan inputs")
        .nth(1)
        .unwrap();
    let example = section
        .split("```lisp\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    run(example);
}

#[test]
fn exclusive_word_reader_helpers_cannot_upgrade_shared_permissions() {
    let source = "(#struct Holder (: value (#ref-mut #u64)))
      (#fn update (: words (#slice-mut #u64)) ()
        (#let restored Holder (#unsafe (#word-read Holder words)))
        (#deref-set (#get restored value) 42u64)
        (#forget restored) (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder (: value (#borrow-mut seed)))))
        (#call update (: words (#borrow-slice-mut words)))
        (#forget words) (#return seed))";
    run(source);
    let invalid = source
        .replace("value (#borrow-mut seed)", "value (#borrow seed)")
        .replace("(#word-write Holder", "(#word-write SharedHolder");
    let invalid = format!("(#struct SharedHolder (: value (#ref #u64))) {invalid}").replace(
        "(#struct-literal Holder (: value (#borrow seed)))",
        "(#struct-literal SharedHolder (: value (#borrow seed)))",
    );
    let error = compile(&invalid).expect_err("numeric backing cannot upgrade a shared loan");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn word_reader_contracts_require_permission_on_every_reaching_branch() {
    let source = "(#struct SharedHolder (: value (#ref #u64)))
      (#struct UniqueHolder (: value (#ref-mut #u64)))
      (#fn fill (: words (#slice-mut #u64) : left (#ref-mut #u64) : right (#ref #u64) : flag #bool) ()
        (#if flag
          (#unsafe (#word-write UniqueHolder words (#struct-literal UniqueHolder (: value left))))
          (#unsafe (#word-write SharedHolder words (#struct-literal SharedHolder (: value right)))))
        (#return ()))
      (#fn update (: words (#slice-mut #u64)) ()
        (#let restored UniqueHolder (#unsafe (#word-read UniqueHolder words)))
        (#deref-set (#get restored value) 42u64) (#forget restored) (#return ()))
      (#fn main () #u64
        (#let-mut left #u64 1u64) (#let right #u64 2u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#call fill (: words (#borrow-slice-mut words) : left (#borrow-mut left)
          : right (#borrow right) : flag true))
        (#call update (: words (#borrow-slice-mut words)))
        (#forget words) (#return left))";
    let error =
        compile(source).expect_err("a shared alternative must not gain exclusive permission");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
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

#[test]
fn contiguous_reference_owner_restoration_keeps_address_and_real_caller_loan() {
    let source = "(#struct Token (: value #u64)) (#linear Token)
      (#struct Owner (: kept (#ref #u64) : item Token))
      (#fn inspect (: owner (#ref Owner)) #u64
        (#return (#u64.+.wrap (#deref (#get owner kept)) (#get (#get owner item) value))))
      (#fn main () #u64
        (#let-mut seed #u64 40u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Owner (#borrow-slice-mut words)
          (#struct-literal Owner (: kept (#borrow seed) : item (#struct-literal Token (: value 1u64))))))
        (#let kept (#ref (#ref #u64))
          (#unsafe (#word-view (#ref (#ref #u64)) (#borrow-slice words 0usize 1usize))))
        (#let moved Token (#unsafe (#word-read Token (#borrow-slice words 1usize 2usize))))
        (#forget moved)
        (#unsafe (#word-write Token (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Token (: value 2u64))))
        (#let whole (#ref Owner) (#unsafe (#word-view (#ref Owner) (#borrow-slice words))))
        (#let selected (#ref (#ref #u64)) (#borrow (#get whole kept)))
        (#assert (#usize.== (#ptr-address (#ref-ptr kept)) (#ptr-address (#ref-ptr selected))))
        (#let answer #u64 (#call inspect (: owner whole)))
        (#forget selected) (#forget whole) (#forget kept) (#forget words)
        (#set seed 0u64) (#return answer))";
    run(source);
    let invalid = source.replace("(#let answer", "(#set seed 0u64) (#let answer");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}
