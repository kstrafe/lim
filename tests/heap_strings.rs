use std::{path::Path, process::Command, time::Duration};

mod support;

fn string_import() -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("library/string.lim")
        .display()
        .to_string()
}

fn compile(source: &str, path: &Path, cache: &Path) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        path,
        &lim::CompileConfig::default(),
        cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn execute(source: &str, label: &str, expected: u8) {
    let scratch = support::Scratch::new(label);
    let assembly = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
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
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected as i32), "{stderr:?}");
    assert!(stdout.is_empty(), "{stdout:?}");
    assert!(stderr.is_empty(), "{stderr:?}");
}

fn rejected(body: &str, label: &str, code: &str, message: &str, fragment: &str) {
    let scratch = support::Scratch::new(label);
    let source = format!("(#import {:?})\n{body}", string_import());
    let diagnostic = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .expect_err("source should be rejected");
    assert_eq!(
        diagnostic.code_string(),
        code,
        "{label}: {}",
        diagnostic.message
    );
    assert!(
        diagnostic.message.contains(message),
        "{label}: {}",
        diagnostic.message
    );
    let span = diagnostic.span.expect("exact offending source span");
    assert_eq!(
        &source[span.start..span.end],
        fragment,
        "{label}: {}",
        diagnostic.message
    );
}

#[test]
fn string_utf8_capacity_mutation_and_clone_contract() {
    let source = format!(
        r#"
      (#import {import:?})
      (#fn main () #u64
        (#let chars (#array #char 3) "Aé🙂")
        (#let-mut text String
          (#match (#call String-from-chars (: text (#slice-of (#borrow chars))))
            (#case (StringCreated owner) owner)
            (#case (StringCreateFailed error) (#panic))))
        (#assert (#usize.== (#call String-len (: string (#borrow text))) 7usize))
        (#assert (#usize.>= (#call String-capacity (: string (#borrow text))) 7usize))
        (#let copy String
          (#match (#call String-try-clone (: string (#borrow text)))
            (#case (StringCreated cloned) cloned)
            (#case (StringCreateFailed error) (#panic))))
        (#assert (#match (#call String-reserve (: string (#borrow-mut text) : additional 64usize))
          (#case StringOk true) (#case _ false)))
        (#let capacity #usize (#call String-capacity (: string (#borrow text))))
        (#let spare (#array #char 2) "xy")
        (#assert (#match (#call String-push-chars (: string (#borrow-mut text) : text (#slice-of (#borrow spare))))
          (#case StringOk true) (#case _ false)))
        (#assert (#usize.== (#call String-len (: string (#borrow text))) 9usize))
        (#assert (#usize.== (#call String-len (: string (#borrow copy))) 7usize))
        (#assert (#match (#call String-byte-at (: string (#borrow text) : index 1usize))
          (#case (StringByte value) (#u8.== value 195u8)) (#case _ false)))
        (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
          (#case (StringPopped value) (#char.== value #\y)) (#case _ false)))
        (#call String-clear (: string (#borrow-mut text)))
        (#assert (#call String-is-empty (: string (#borrow text))))
        (#assert (#usize.== (#call String-capacity (: string (#borrow text))) capacity))
        (#assert (#match (#call String-push-chars (: string (#borrow-mut text) : text (#slice-of (#borrow chars))))
          (#case StringOk true) (#case _ false)))
        (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
          (#case (StringPopped value) (#char.== value #\🙂)) (#case _ false)))
        (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
          (#case (StringPopped value) (#char.== value #\é)) (#case _ false)))
        (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
          (#case (StringPopped value) (#char.== value #\A)) (#case _ false)))
        (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
          (#case StringEmpty true) (#case _ false)))
        (#let moved String text)
        (#call String-free (: string moved))
        (#call String-free (: string copy))
        (#return 42u64))
    "#,
        import = string_import()
    );
    execute(&source, "heap-string-roundtrip", 42);
}

#[test]
fn string_utf8_validation_matrix_and_embedded_nul() {
    let source = format!(
        r#"
      (#import {import:?})
      (#fn valid ((bytes (#slice #u8))) #bool
        (#return (#match (#call String-from-utf8 (: bytes bytes))
          (#case (StringCreated text) (#block (#call String-free (: string text)) true))
          (#case _ false))))
      (#fn main () #u64
        (#let nul (#array #u8 3) (#array-of (#array #u8 3) 65u8 0u8 66u8))
        (#let good (#array #u8 4) (#array-of (#array #u8 4) 240u8 159u8 153u8 130u8))
        (#let overlong (#array #u8 2) (#array-of (#array #u8 2) 192u8 175u8))
        (#let surrogate (#array #u8 3) (#array-of (#array #u8 3) 237u8 160u8 128u8))
        (#let truncated (#array #u8 2) (#array-of (#array #u8 2) 226u8 130u8))
        (#let too-large (#array #u8 4) (#array-of (#array #u8 4) 244u8 144u8 128u8 128u8))
        (#assert (#call valid (: bytes (#slice-of (#borrow nul)))))
        (#assert (#call valid (: bytes (#slice-of (#borrow good)))))
        (#assert (#bool.! (#call valid (: bytes (#slice-of (#borrow overlong))))))
        (#assert (#bool.! (#call valid (: bytes (#slice-of (#borrow surrogate))))))
        (#assert (#bool.! (#call valid (: bytes (#slice-of (#borrow truncated))))))
        (#assert (#bool.! (#call valid (: bytes (#slice-of (#borrow too-large))))))
        (#return 42u64))
    "#,
        import = string_import()
    );
    execute(&source, "heap-string-utf8-matrix", 42);
}

#[test]
fn utf8_boundaries_roundtrip_bytes_and_reject_malformed_sequences() {
    let cases: &[(&[u8], bool)] = &[
        (&[], true),
        (&[0, 0x7f], true),
        (&[0xc2, 0x80], true),
        (&[0xdf, 0xbf], true),
        (&[0xe0, 0xa0, 0x80], true),
        (&[0xed, 0x9f, 0xbf], true),
        (&[0xee, 0x80, 0x80], true),
        (&[0xef, 0xbf, 0xbf], true),
        (&[0xf0, 0x90, 0x80, 0x80], true),
        (&[0xf4, 0x8f, 0xbf, 0xbf], true),
        (&[0x80], false),
        (&[0xbf], false),
        (&[0xc0, 0x80], false),
        (&[0xc1, 0xbf], false),
        (&[0xc2], false),
        (&[0xc2, 0x7f], false),
        (&[0xe0, 0x9f, 0xbf], false),
        (&[0xed, 0xa0, 0x80], false),
        (&[0xed, 0xbf, 0xbf], false),
        (&[0xe1, 0x80], false),
        (&[0xe1, 0x80, 0xc0], false),
        (&[0xf0, 0x8f, 0xbf, 0xbf], false),
        (&[0xf4, 0x90, 0x80, 0x80], false),
        (&[0xf1, 0x80, 0x80], false),
        (&[0xf1, 0x80, 0x80, 0x7f], false),
        (&[0xf5, 0x80, 0x80, 0x80], false),
        (&[0xfe], false),
        (&[0xff], false),
        (&[b'a', 0xc2], false),
    ];
    let mut source = format!("(#import {:?})\n", string_import());
    source.push_str(r#"
      (#fn check-valid (: input (#slice #u8)) #bool
        (#return (#match (#call String-from-utf8 (: bytes input))
          (#case (StringCreated text)
            (#block
              (#let view StringBytes (#call String-bytes (: string (#borrow text))))
              (#let length #usize (#call StringBytes-len (: bytes view)))
              (#assert (#usize.== length (#slice-len input)))
              (#let-mut cursor #usize 0usize)
              (#while (#usize.< cursor length)
                (#assert (#match (#call StringBytes-byte-at (: bytes view : index cursor))
                  (#case (StringByte byte) (#u8.== byte (#deref (#slice-idx input cursor))))
                  (#case StringByteOutOfBounds false)))
                (#set cursor (#usize.+.wrap cursor 1usize)))
              (#assert (#match (#call StringBytes-byte-at (: bytes view : index length))
                (#case StringByteOutOfBounds true) (#case _ false)))
              (#assert (#match (#call StringBytes-byte-at (: bytes view : index 18446744073709551615usize))
                (#case StringByteOutOfBounds true) (#case _ false)))
              (#drop view)
              (#call String-free (: string text))
              true))
          (#case (StringCreateFailed error) false))))
      (#fn check-invalid (: input (#slice #u8)) #bool
        (#return (#match (#call String-from-utf8 (: bytes input))
          (#case (StringCreated text) (#block (#call String-free (: string text)) false))
          (#case (StringCreateFailed error) (#match error
            (#case StringInvalidUtf8 true) (#case _ false))))))
      (#fn main () #u64
    "#);
    for (index, (bytes, valid)) in cases.iter().enumerate() {
        let size = bytes.len().max(1);
        let values = if bytes.is_empty() {
            "0u8".to_owned()
        } else {
            bytes
                .iter()
                .map(|b| format!("{b}u8"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        let input = if bytes.is_empty() {
            format!("(#slice-range (#slice-of (#borrow input{index})) 0usize 0usize)")
        } else {
            format!("(#slice-of (#borrow input{index}))")
        };
        let check = if *valid {
            "check-valid"
        } else {
            "check-invalid"
        };
        source.push_str(&format!("(#let input{index} (#array #u8 {size}) (#array-of (#array #u8 {size}) {values}))\n(#assert (#call {check} (: input {input})))\n"));
    }
    source.push_str("(#return 42u64))");
    execute(&source, "string-utf8-boundaries", 42);
}

#[test]
fn character_encoding_and_popping_cover_every_utf8_width_and_invalid_scalars() {
    let source = format!(
        r#"
      (#import {import:?})
      (#fn main () #u64
        (#let values (#array #u32 10) (#array-of (#array #u32 10)
          0u32 127u32 128u32 2047u32 2048u32 55295u32 57344u32 65535u32 65536u32 1114111u32))
        (#let widths (#array #usize 10) (#array-of (#array #usize 10)
          1usize 1usize 2usize 2usize 3usize 3usize 3usize 3usize 4usize 4usize))
        (#let-mut text String (#call String-new ()))
        (#let-mut index #usize 0usize)
        (#while (#usize.< index 10usize)
          (#let code #u32 (#index values index))
          (#assert (#match (#call String-push-char (: string (#borrow-mut text) : value (#as code #char)))
            (#case StringOk true) (#case _ false)))
          (#assert (#usize.== (#call String-len (: string (#borrow text))) (#index widths index)))
          (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
            (#case (StringPopped value) (#u32.== (#as value #u32) code)) (#case _ false)))
          (#assert (#call String-is-empty (: string (#borrow text))))
          (#set index (#usize.+.wrap index 1usize)))
        (#let invalid (#array #u32 3) (#array-of (#array #u32 3) 55296u32 57343u32 1114112u32))
        (#let capacity #usize (#call String-capacity (: string (#borrow text))))
        (#let-mut invalid-index #usize 0usize)
        (#while (#usize.< invalid-index 3usize)
          (#assert (#match (#call String-push-char (: string (#borrow-mut text) : value (#as (#index invalid invalid-index) #char)))
            (#case (StringErr StringInvalidChar) true) (#case _ false)))
          (#set invalid-index (#usize.+.wrap invalid-index 1usize)))
        (#let invalid-text (#array #char 2) (#array-of (#array #char 2) (#as 97u32 #char) (#as 55296u32 #char)))
        (#assert (#match (#call String-push-chars (: string (#borrow-mut text) : text (#slice-of (#borrow invalid-text))))
          (#case (StringErr StringInvalidChar) true) (#case _ false)))
        (#assert (#call String-is-empty (: string (#borrow text))))
        (#assert (#usize.== (#call String-capacity (: string (#borrow text))) capacity))
        (#let view StringBytes (#call String-bytes (: string (#borrow text))))
        (#assert (#usize.== (#call StringBytes-len (: bytes view)) 0usize))
        (#drop view)
        (#call String-clear (: string (#borrow-mut text)))
        (#call String-free (: string text))
        (#return 42u64))
    "#,
        import = string_import()
    );
    execute(&source, "string-scalar-boundaries", 42);
}

#[test]
fn returned_and_copied_byte_views_retain_the_owner_borrow() {
    let source = format!(
        r#"
      (#import {import:?})
      (#fn view-of (: string (#ref String)) StringBytes
        (#return (#call String-bytes (: string string))))
      (#fn main () #u64
        (#let-mut text String (#call String-new ()))
        (#assert (#match (#call String-push-char (: string (#borrow-mut text) : value (#as 65u32 #char)))
          (#case StringOk true) (#case _ false)))
        (#let original StringBytes (#call view-of (: string (#borrow text))))
        (#let copy StringBytes (#clone original))
        (#drop original)
        (#assert (#usize.== (#call StringBytes-len (: bytes copy)) 1usize))
        (#assert (#match (#call StringBytes-byte-at (: bytes copy : index 0usize))
          (#case (StringByte byte) (#u8.== byte 65u8)) (#case _ false)))
        (#drop copy)
        (#call String-clear (: string (#borrow-mut text)))
        (#call String-free (: string text))
        (#return 42u64))
    "#,
        import = string_import()
    );
    execute(&source, "string-returned-byte-view", 42);
}

#[test]
fn string_linear_ownership_and_borrow_diagnostics() {
    rejected(
        "(#fn main () #u64 (#let text String (#call String-new ())) (#return 42u64))",
        "string-leak",
        "E4200",
        "must be consumed before returning",
        "text",
    );
    rejected("(#fn main () #u64 (#let text String (#call String-new ())) (#call String-free (: string text)) (#call String-free (: string text)) (#return 42u64))",
        "string-use-after-free", "E4200", "was used more than once", "text");
    rejected("(#fn main () #u64 (#let text String (#call String-new ())) (#let copy String (#clone text)) (#call String-free (: string text)) (#call String-free (: string copy)) (#return 42u64))",
        "string-direct-clone", "E4000", "opaque", "(#clone text)");
    rejected("(#fn main () #u64 (#let text String (#struct-literal String (: pointer (#ptr-null (#ptr-mut #u8)) : length 0usize : capacity 0usize))) (#call String-free (: string text)) (#return 42u64))",
        "string-forged-owner", "E4000", "cannot construct opaque type 'String'", "String");
    rejected("(#fn main () #u64 (#let text String (#call String-new ())) (#let pointer (#ptr-mut #u8) (#get text pointer)) (#call String-free (: string text)) (#return 42u64))",
        "string-exposed-pointer", "E4000", "cannot access fields of opaque type 'String'", "pointer");
    rejected("(#fn dangling () StringBytes (#let text String (#call String-new ())) (#let view StringBytes (#call String-bytes (: string (#borrow text)))) (#forget text) (#return view))",
        "string-dead-byte-view", "E4200", "returned reference may point to a consumed linear referent", "(#return view)");
    for operation in [
        "(#call String-clear (: string (#borrow-mut text)))",
        "(#call String-free (: string text))",
    ] {
        let cleanup = if operation.contains("String-clear") {
            "(#forget text)"
        } else {
            "()"
        };
        let body = format!(
            "(#fn main () #u64
          (#let-mut text String (#call String-new ()))
          (#let bytes StringBytes (#call String-bytes (: string (#borrow text))))
          {operation}
          (#let length #usize (#call StringBytes-len (: bytes bytes)))
          (#drop bytes)
          {cleanup}
          (#return (#as length #u64)))"
        );
        let (label, message, fragment) = if operation.contains("String-clear") {
            (
                "string-live-byte-mutation",
                "cannot borrow 'text' mutably",
                "#borrow-mut",
            )
        } else {
            ("string-live-byte-free", "cannot move", "text")
        };
        rejected(&body, label, "E4100", message, fragment);
    }
}

#[test]
fn example_source_compiles_and_runs_as_documented() {
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/heap_string.lim");
    let source = std::fs::read_to_string(&example).unwrap();
    let scratch = support::Scratch::new("heap-string-example");
    let assembly = compile(&source, &example, &scratch.path().join("cache"))
        .unwrap_or_else(|error| panic!("{}", error.message));
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
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert_eq!(stdout, "Heap: naïve 🙂\n".as_bytes());
    assert!(stderr.is_empty(), "{stderr:?}");
}
