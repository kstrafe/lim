#[path = "support/generated_source.rs"]
mod generated_source;
mod support;
use std::{fs, path::Path, process::Command, time::Duration};

fn compile(source: &str, path: &Path) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        path,
        &lim::CompileConfig::default(),
        &path.parent().unwrap().join(".lim/cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}
fn execute(source: &str, label: &str) {
    let scratch = support::Scratch::new(label);
    let assembly = compile(source, &scratch.path().join("main.lim"))
        .unwrap_or_else(|error| panic!("{label}: {}", error.message));
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
        support::run(&mut Command::new(binary), Duration::from_secs(10), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{label}: {stderr:?}");
    assert!(stdout.is_empty(), "{stdout:?}");
    assert!(stderr.is_empty(), "{stderr:?}");
}

#[test]
fn string_view_example_runs_with_bundled_sources_outside_the_checkout() {
    execute(
        include_str!("../examples/string_view.lim"),
        "utf8-view-example",
    );
}

#[test]
fn slice_validation_and_scalar_iteration_match_the_rust_utf8_oracle() {
    let mut cases = vec![
        vec![],
        vec![0],
        vec![127],
        b"A\0B".to_vec(),
        "Aéλ🙂!".as_bytes().to_vec(),
    ];
    for scalar in [
        0x80, 0x7ff, 0x800, 0xd7ff, 0xe000, 0xffff, 0x10000, 0x10ffff,
    ] {
        let mut bytes = [0; 4];
        cases.push(
            char::from_u32(scalar)
                .unwrap()
                .encode_utf8(&mut bytes)
                .as_bytes()
                .to_vec(),
        );
    }
    for bytes in [
        &[0x80][..],
        &[0xbf],
        &[0xc0, 0x80],
        &[0xc1, 0xbf],
        &[0xc2],
        &[0xc2, 0x7f],
        &[0xe0, 0x9f, 0xbf],
        &[0xed, 0xa0, 0x80],
        &[0xed, 0xbf, 0xbf],
        &[0xe1, 0x80],
        &[0xe1, 0x80, 0xc0],
        &[0xf0, 0x8f, 0xbf, 0xbf],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xf1, 0x80, 0x80],
        &[0xf1, 0x80, 0x80, 0x7f],
        &[0xf5, 0x80, 0x80, 0x80],
        &[0xfe],
        &[0xff],
        &[b'a', 0xc2],
    ] {
        cases.push(bytes.to_vec());
    }
    // Deterministic extra mixed sequences, not a second hand-written validator.
    let mut state = 0x1357_2468u32;
    for length in 1..=4 {
        for _ in 0..24 {
            let mut bytes = Vec::new();
            for _ in 0..length {
                state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                bytes.push((state >> 24) as u8);
            }
            cases.push(bytes);
        }
    }
    // Keep each checked program small while retaining every oracle case.
    for batch in cases.chunks(8) {
        let mut source = "#std\n#fn main {\n  #params = ();\n  #returns = #u64;\n\n  #body = (\n".to_owned();
        for (i, bytes) in batch.iter().enumerate() {
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
            source.push_str(&format!(
                "  (#let input{i} (#array #u8 {size}) (#array-of (#array #u8 {size}) {values}))\n"
            ));
            let slice = if bytes.is_empty() {
                format!("(#slice-range (#slice-of (#borrow input{i})) 0usize 0usize)")
            } else {
                format!("(#slice-of (#borrow input{i}))")
            };
            source.push_str(&format!(
            "  (#let result{i} Utf8Slice::Result (#call Utf8Slice::from-owner ((owner {slice}))))\n"
        ));
            match std::str::from_utf8(bytes) {
            Ok(text) => {
                source.push_str(&format!("  (#let view{i} Utf8Slice (#match result{i} (#case (Utf8Slice::Result.Valid accepted{i}) accepted{i}) (#case _ (#panic))))\n"));
                source.push_str(&format!("  (#assert (#usize::eq (#call Utf8Slice::len ((view (#borrow view{i})))) {}usize))\n", bytes.len()));
                for (offset, byte) in bytes.iter().enumerate() {
                    source.push_str(&format!("  (#assert (#match (#call Utf8Slice::byte-at ((view (#borrow view{i})) (index {offset}usize))) (#case (Utf8ByteResult.Utf8Byte copied{i}_{offset}) (#u8::eq copied{i}_{offset} {byte}u8)) (#case _ false)))\n"));
                }
                source.push_str(&format!("  (#assert (#match (#call Utf8Slice::byte-at ((view (#borrow view{i})) (index {}usize))) (#case Utf8ByteResult.Utf8ByteOutOfBounds true) (#case _ false)))\n", bytes.len()));
                source.push_str(&format!(
                    "  (#let-mut chars{i} Utf8Slice::Chars (#call Utf8Slice::chars ((view view{i}))))\n"
                ));
                for (j, scalar) in text.chars().enumerate() {
                    source.push_str(&format!("  (#assert (#match (#call Utf8Slice::Chars::next ((iterator (#borrow-mut chars{i})))) (#case (Utf8Slice::CharResult.Char scalar{i}_{j}) (#u32::eq (#as scalar{i}_{j} #u32) {}u32)) (#case _ false)))\n", scalar as u32));
                }
                for _ in 0..2 {
                    source.push_str(&format!("  (#assert (#match (#call Utf8Slice::Chars::next ((iterator (#borrow-mut chars{i})))) (#case Utf8Slice::CharResult.End true) (#case _ false)))\n"));
                }
                source.push_str(&format!("  (#forget chars{i})\n"));
            }
            Err(_) => source.push_str(&format!(
                "  (#assert (#match result{i} (#case Utf8Slice::Result.InvalidUtf8 true) (#case _ false)))\n"
            )),
        }
        }
        source.push_str("  (#return 42u64)\n\n  );\n}\n");
        execute(&source, "utf8-slice-oracle");
    }
}

#[test]
fn every_subview_range_matches_rust_boundaries_for_both_storage_layouts() {
    let bytes = "A\0é€😀!".as_bytes();
    let mut base = format!(
        "#std\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of String::from-utf8) (#effects-of String::free) (#effects-of String::view) (#effects-of StringView::subview)); #body = (\n  (#let bytes (#array #u8 {}) (#array-of (#array #u8 {}) {}))\n",
        bytes.len(),
        bytes.len(),
        bytes
            .iter()
            .map(|b| format!("{b}u8"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    base.push_str("  (#let text String (#match (#call String::from-utf8 ((bytes (#slice-of (#borrow bytes))))) (#case (StringCreateResult.StringCreated created) created) (#case _ (#panic))))\n  (#let string-view StringView (#call String::view ((string (#borrow text)))))\n  (#let slice-view Utf8Slice (#match (#call Utf8Slice::from-owner ((owner (#slice-of (#borrow bytes))))) (#case (Utf8Slice::Result.Valid accepted) accepted) (#case _ (#panic))))\n");
    let text = std::str::from_utf8(bytes).unwrap();
    for (prefix, variable) in [("StringView", "string-view"), ("Utf8Slice", "slice-view")] {
        for start in 0..=bytes.len() + 1 {
            let mut source = base.clone();
            for end in 0..=bytes.len() + 1 {
                let tag = if start > end || end > bytes.len() {
                    "InvalidRange"
                } else if !text.is_char_boundary(start) || !text.is_char_boundary(end) {
                    "InvalidBoundary"
                } else {
                    "Valid"
                };
                let branch = if tag == "Valid" {
                    format!("(#case ({prefix}::Result.Valid selected) (#block (#assert (#usize::eq (#call {prefix}::len ((view (#borrow selected)))) {}usize)) (#forget selected) true))", end - start)
                } else {
                    format!("(#case {prefix}::Result.{tag} true)")
                };
                // Each match binding gets its own scope; no enclosing shadowing.
                source.push_str(&format!("  (#assert (#match (#call {prefix}::subview ((view (#borrow {variable})) (start {start}usize) (end {end}usize))) {branch} (#case _ false)))\n"));
            }
            source.push_str(&format!("  (#assert (#match (#call {prefix}::subview ((view (#borrow {variable})) (start 0usize) (end 18446744073709551615usize))) (#case {prefix}::Result.InvalidRange true) (#case _ false)))\n"));
            source.push_str("  (#forget slice-view) (#forget string-view) (#call String::free ((string text))) (#return 42u64)\n  );\n}\n");
            execute(&source, "utf8-all-boundaries");
        }
    }
}

#[test]
fn nested_views_and_iterators_keep_the_source_borrow_not_temporary_containers() {
    execute(
        r#"#std
#struct StoredView () ((contents StringView))
#fn middle {
  #params = ((owner (#ref String)));
  #returns = StoredView;
  #effects = ((#effects-of String::view) (#effects-of StringView::subview)); #body = (
          (#let parent StringView (#call String::view ((string owner))))
          (#let child StringView (#match (#call StringView::subview ((view (#borrow parent)) (start 1usize) (end 3usize)))
            (#case (StringView::Result.Valid selected) selected) (#case _ (#panic))))
          (#forget parent)
          (#return (#struct-literal StoredView ((contents child))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of String::free) (#effects-of String::from-chars) (#effects-of StringView::Chars::next) (#effects-of StringView::subview) (#effects-of middle)); #body = (
          (#let chars (#array #char 3) "Aé!")
          (#let-mut text String (#match (#call String::from-chars ((text (#slice-of (#borrow chars)))))
            (#case (StringCreateResult.StringCreated created) created) (#case _ (#panic))))
          (#let stored StoredView (#call middle ((owner (#borrow text)))))
          (#let copied StringView (#call StringView::clone ((view (#borrow (#get stored contents))))))
          (#forget stored)
          (#let nested StringView (#match (#call StringView::subview ((view (#borrow copied)) (start 0usize) (end 2usize)))
            (#case (StringView::Result.Valid selected) selected) (#case _ (#panic))))
          (#forget copied)
          (#let-mut iterator StringView::Chars (#call StringView::chars ((view nested))))
          (#assert (#match (#call StringView::Chars::next ((iterator (#borrow-mut iterator))))
            (#case (StringView::CharResult.Char value) (#char::eq value #\é)) (#case _ false)))
          (#forget iterator)
          (#call String::clear ((string (#borrow-mut text))))
          (#call String::free ((string text)))
          (#return 42u64)
  );
}
"#,
        "utf8-nested-returned-view",
    );
}

#[test]
fn empty_string_view_and_empty_subview_retain_borrows_and_iterate_to_end() {
    execute(
        r#"#std
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of String::free) (#effects-of String::view) (#effects-of StringView::Chars::next) (#effects-of StringView::subview)); #body = (
        (#let text String (#call String::new ()))
        (#let whole StringView (#call String::view ((string (#borrow text)))))
        (#assert (#call StringView::is-empty ((view (#borrow whole)))))
        (#let empty StringView (#match (#call StringView::subview ((view (#borrow whole)) (start 0usize) (end 0usize)))
          (#case (StringView::Result.Valid selected) selected) (#case _ (#panic))))
        (#forget whole)
        (#let-mut iterator StringView::Chars (#call StringView::chars ((view empty))))
        (#assert (#match (#call StringView::Chars::next ((iterator (#borrow-mut iterator))))
          (#case StringView::CharResult.End true) (#case _ false)))
        (#forget iterator) (#call String::free ((string text))) (#return 42u64)
  );
}
"#,
        "utf8-empty-view",
    );
}

#[test]
fn string_and_slice_views_reject_mutation_destruction_and_source_escape() {
    let setups = [
        "(#let view StringView (#call String::view ((string (#borrow text)))))",
        "(#let parent StringView (#call String::view ((string (#borrow text))))) (#let view StringView (#match (#call StringView::subview ((view (#borrow parent)) (start 0usize) (end 0usize))) (#case (StringView::Result.Valid selected) selected) (#case _ (#panic)))) (#forget parent)",
    ];
    for (i, setup) in setups.iter().enumerate() {
        for (j, mutation) in [
            "(#call String::clear ((string (#borrow-mut text))))",
            "(#call String::reserve ((string (#borrow-mut text)) (additional 64usize)))",
            "(#call String::free ((string text)))",
            "(#let moved String text)",
        ]
        .iter()
        .enumerate()
        {
            let cleanup = match j {
                0 | 1 => "(#call String::free ((string text)))",
                2 => "",
                _ => "(#call String::free ((string moved)))",
            };
            let source = format!("#std\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let-mut text String (#call String::new ())) {setup} {mutation} (#let size #usize (#call StringView::len ((view (#borrow view))))) (#forget view) {cleanup} (#return 42u64)\n  );\n}}\n");
            let scratch = support::Scratch::new(&format!("utf8-borrow-{i}-{j}"));
            let error = compile(&source, &scratch.path().join("main.lim")).unwrap_err();
            assert_eq!(error.code_string(), "E4100", "{}", error.message);
            let span = error.span.expect("offending source span");
            assert!(
                span.start >= source.find(mutation).unwrap()
                    && span.end <= source.find(mutation).unwrap() + mutation.len(),
                "{}: {:?}",
                error.message,
                span
            );
        }
    }
    for (label, source) in [
        ("iterator", "#std\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of String::free) (#effects-of String::view) (#effects-of StringView::Chars::next)); #body = ( (#let-mut text String (#call String::new ())) (#let whole StringView (#call String::view ((string (#borrow text))))) (#let-mut iterator StringView::Chars (#call StringView::chars ((view whole)))) (#call String::free ((string text))) (#call StringView::Chars::next ((iterator (#borrow-mut iterator)))) (#forget iterator) (#return 42u64)\n  );\n}\n"),
        ("returned", "#std\n#fn bad {\n  #params = ();\n  #returns = StringView;\n  #effects = ((#effects-of String::view)); #body = ( (#let text String (#call String::new ())) (#let view StringView (#call String::view ((string (#borrow text))))) (#forget text) (#return view)\n  );\n}\n"),
        ("slice", "#std\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let-mut bytes (#array #u8 1) (#array-of (#array #u8 1) 65u8)) (#let view Utf8Slice (#match (#call Utf8Slice::from-owner ((owner (#slice-of (#borrow bytes))))) (#case (Utf8Slice::Result.Valid selected) selected) (#case _ (#panic)))) (#let change (#ref-mut (#array #u8 1)) (#borrow-mut bytes)) (#call Utf8Slice::len ((view (#borrow view)))) (#forget view) (#return 42u64)\n  );\n}\n"),
        ("slice-returned", "#std\n#fn bad {\n  #params = ();\n  #returns = Utf8Slice;\n  #body = ( (#let bytes (#array #u8 1) (#array-of (#array #u8 1) 65u8)) (#return (#match (#call Utf8Slice::from-owner ((owner (#slice-of (#borrow bytes))))) (#case (Utf8Slice::Result.Valid selected) selected) (#case _ (#panic))))\n  );\n}\n"),
    ] {
        let scratch = support::Scratch::new(&format!("utf8-reject-{label}"));
        let error = compile(source, &scratch.path().join("main.lim")).unwrap_err();
        // Consumption-before-return is caught by ownership validation before
        // the escape checker; it must still diagnose the actual referent loan.
        let expected = if label == "returned" { "E4200" } else { "E4100" };
        assert_eq!(error.code_string(), expected, "{label}: {}", error.message);
        if label == "returned" {
            assert!(error.message.contains("consumed linear referent"), "{}", error.message);
        }
        assert!(error.span.is_some(), "{label}: {}", error.message);
    }
}

#[test]
fn generated_views_are_cached_inspectable_and_compile_as_ordinary_lim() {
    let scratch = support::Scratch::new("utf8-inspectable");
    let path = scratch.path().join("main.lim");
    let source = "#std\n#generate #utf8-view ((name BorrowedText) (owner (#slice #u8)))\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n";
    fs::write(&path, source).unwrap();
    let first = compile(source, &path).unwrap();
    let generated_dir = scratch.path().join(".lim/generated");
    let generated = fs::read_dir(&generated_dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .find(|p| {
            fs::read_to_string(p)
                .unwrap()
                .contains("#struct BorrowedText ")
        })
        .expect("inspectable custom view source");
    let artifact = fs::read_to_string(&generated).unwrap();
    let text = generated_source::ordinary_source(&artifact);
    let modified = fs::metadata(&generated).unwrap().modified().unwrap();
    assert!(text.contains(&format!("{}:2", path.display())));
    assert!(!text.contains("#generate "));
    assert_eq!(first, compile(source, &path).unwrap());
    assert_eq!(
        modified,
        fs::metadata(&generated).unwrap().modified().unwrap()
    );
    execute(&format!("#std\n{text}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let bytes (#array #u8 1) (#array-of (#array #u8 1) 65u8)) (#let view BorrowedText (#match (#call BorrowedText::from-owner ((owner (#slice-of (#borrow bytes))))) (#case (BorrowedText::Result.Valid accepted) accepted) (#case _ (#panic)))) (#assert (#usize::eq (#call BorrowedText::len ((view (#borrow view)))) 1usize)) (#forget view) (#return 42u64)\n  );\n}}\n"), "utf8-emitted-source");
}

#[test]
fn assume_valid_requires_unsafe_and_unstable_owner_types_fail_at_the_invocation() {
    let scratch = support::Scratch::new("utf8-unsafe-contract");
    let source = "#std\n#fn bad {\n  #params = ((owner (#slice #u8)));\n  #returns = Utf8Slice;\n  #body = ( (#return (#unsafe-call Utf8Slice::assume-valid ((owner owner))))\n  );\n}\n";
    let error = compile(source, &scratch.path().join("main.lim")).unwrap_err();
    assert_eq!(error.code_string(), "E4300", "{}", error.message);
    assert!(error.message.contains("unsafe"));
    let source = "#std\n#generate #utf8-view ((name Unsupported) (owner (#ref #u8)))\n";
    let error = compile(source, &scratch.path().join("main.lim")).unwrap_err();
    assert_eq!(error.code_string(), "E3000", "{}", error.message);
    assert!(error.message.contains("utf8-view owner must"));
    assert_eq!(
        &source[error.span.unwrap().start..error.span.unwrap().end],
        "#generate #utf8-view ((name Unsupported) (owner (#ref #u8)))"
    );
}
