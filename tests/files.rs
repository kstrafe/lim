mod support;
use std::{fs, process::Command, time::Duration};

fn execute(source: &str, scratch: &support::Scratch) {
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, errors) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        65536,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&errors));
    let (status, _, errors) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&errors)
    );
}

#[test]
fn minimal_std_entry_compiles_with_the_file_api_loaded() {
    let scratch = support::Scratch::new("file-std-minimal");
    let source = "(#std) (#fn main () #u64 (#return 42u64))";
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    assert!(!assembly.is_empty());
}

fn path_binding(path: &std::path::Path) -> String {
    let value = path.to_str().unwrap();
    format!("(#let chars (#array #char {}) {value:?})\n(#let created StringCreateResult (#call String::from-chars (: text (#slice-of (#borrow chars)))))\n(#let-else (StringCreateResult.StringCreated path) StringCreateResult created (#unreachable))", value.chars().count())
}

#[test]
fn buffered_binary_reads_cross_refill_boundaries_and_preserve_eof() {
    for capacity in [1, 3, 64] {
        for data in [vec![], vec![0, 255, 65, 128, 10, 42, 0]] {
            let scratch = support::Scratch::new("file-buffer");
            let path = scratch.path().join("binary-λ");
            fs::write(&path, &data).unwrap();
            let checks = data.iter().map(|byte| format!(
                "(#assert (#match (#call FileReader::next-byte (: reader (#borrow-mut reader)))\n(#case (FileByteResult.FileByte byte) (#u8::eq byte {byte}u8)) (#case _ false)))"
            )).collect::<Vec<_>>().join("\n");
            execute(&format!("(#std) (#fn main () #u64\n{}\n\
                (#let opened FileOpenResult (#call File::open-read (: path (#borrow path))))\n\
                (#call String::free (: string path))\n\
                (#let-else (FileOpenResult.FileOpened file) FileOpenResult opened (#unreachable))\n\
                (#let buffered FileReaderCreateResult (#call FileReader::create (: file file : capacity {capacity}usize)))\n\
                (#let-else (FileReaderCreateResult.FileReaderCreated initial) FileReaderCreateResult buffered (#unreachable))\n\
                (#let-mut reader FileReader initial)\n{checks}\n\
                (#assert (#match (#call FileReader::next-byte (: reader (#borrow-mut reader))) (#case FileByteResult.FileByteEof true) (#case _ false)))\n\
                (#assert (#match (#call FileReader::next-byte (: reader (#borrow-mut reader))) (#case FileByteResult.FileByteEof true) (#case _ false)))\n\
                (#assert (#match (#call FileReader::close (: reader reader)) (#case FileStatus.FileOk true) (#case _ false)))\n\
                (#return 42u64))", path_binding(&path)), &scratch);
        }
    }
}

#[test]
fn file_creation_writes_utf8_nul_and_closes_explicitly() {
    let scratch = support::Scratch::new("file-write");
    let path = scratch.path().join("output");
    execute(&format!("(#std) (#fn main () #u64\n{}\n\
        (#let opened FileOpenResult (#call File::create (: path (#borrow path) : permissions 384u32)))\n\
        (#call String::free (: string path))\n\
        (#let-else (FileOpenResult.FileOpened initial) FileOpenResult opened (#unreachable))\n\
        (#let-mut file File initial)\n\
        (#let text-chars (#array #char 4) \"Aλ\\u{{0}}Z\")\n\
        (#let text-created StringCreateResult (#call String::from-chars (: text (#slice-of (#borrow text-chars)))))\n\
        (#let-else (StringCreateResult.StringCreated text) StringCreateResult text-created (#unreachable))\n\
        (#assert (#match (#call File::write-string (: file (#borrow-mut file) : text (#borrow text)))\n\
          (#case (FileWriteResult.FileWritten count) (#usize::eq count 5usize)) (#case _ false)))\n\
        (#call String::free (: string text))\n\
        (#assert (#match (#call File::close (: file file)) (#case FileStatus.FileOk true) (#case _ false)))\n\
        (#return 42u64))", path_binding(&path)), &scratch);
    assert_eq!(fs::read(path).unwrap(), "Aλ\0Z".as_bytes());
}

#[test]
fn missing_paths_and_invalid_buffer_sizes_are_explicit_errors() {
    let scratch = support::Scratch::new("file-errors");
    let missing = scratch.path().join("missing");
    execute(&format!("(#std)
        (#fn is-missing-file-error (: error FileError) #bool
          (#return (#match error
            (#case (FileError.FileIoError code) (#i64::eq code -2i64))
            (#case _ false))))
        (#fn closes-successfully (: file File) #bool
          (#return (#match (#call File::close (: file file))
            (#case FileStatus.FileOk true) (#case _ false))))
        (#fn main () #u64
 {}\n\
        (#let opened FileOpenResult (#call File::open-read (: path (#borrow path))))\n\
        (#call String::free (: string path))\n\
        (#assert (#match opened (#case (FileOpenResult.FileOpenFailed failure) (#call is-missing-file-error (: error failure)))\n\
          (#case (FileOpenResult.FileOpened unexpected) (#block (#call closes-successfully (: file unexpected)) false))\n\
          (#case _ false))) (#return 42u64))", path_binding(&missing)), &scratch);
    let existing = scratch.path().join("existing");
    fs::write(&existing, b"data").unwrap();
    execute(&format!("(#std)
        (#fn is-invalid-system-allocation-size (: error SystemAllocationError) #bool
          (#return (#match error
            (#case SystemAllocationError.SystemAllocationInvalidSize true)
            (#case _ false))))
        (#fn is-invalid-size-error (: error FileError) #bool
          (#return (#match error
            (#case (FileError.FileAllocationError allocation-error)
              (#call is-invalid-system-allocation-size (: error allocation-error)))
            (#case _ false))))
        (#fn closes-successfully (: file File) #bool
          (#return (#match (#call File::close (: file file))
            (#case FileStatus.FileOk true) (#case _ false))))
        (#fn main () #u64
 {}\n\
        (#let opened FileOpenResult (#call File::open-read (: path (#borrow path))))\n\
        (#call String::free (: string path))\n\
        (#let-else (FileOpenResult.FileOpened file) FileOpenResult opened (#unreachable))\n\
        (#let failed FileReaderCreateResult (#call FileReader::create (: file file : capacity 0usize)))\n\
        (#assert (#match failed\n\
          (#case (FileReaderCreateResult.FileReaderCreateFailed (FileReaderCreateFailure retained error))\n\
            (#block\n\
              (#let invalid-size #bool (#call is-invalid-size-error (: error error)))\n\
              (#let closed #bool (#call closes-successfully (: file retained)))\n\
              (#bool::and invalid-size closed)))\n\
          (#case (FileReaderCreateResult.FileReaderCreated unexpected)\n\
            (#block (#call FileReader::close (: reader unexpected)) false))))\n\
        (#return 42u64))", path_binding(&existing)), &scratch);
}

#[test]
fn files_cannot_be_duplicated_abandoned_or_closed_while_borrowed() {
    let scratch = support::Scratch::new("file-ownership");
    for (name, body, expected) in [
        (
            "double-close",
            "(#call File::close (: file file)) (#call File::close (: file file))",
            lim::DiagnosticCode::Linear,
        ),
        ("abandon", "()", lim::DiagnosticCode::Linear),
        (
            "close-borrowed",
            "(#let view (#ref File) (#borrow file)) (#call File::close (: file file)) (#drop view)",
            lim::DiagnosticCode::Borrow,
        ),
    ] {
        let source = format!("(#std) (#fn bad (: file File) () {body} (#return ())) (#fn main () #u64 (#return 0u64))");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("case.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(error.code, expected, "{name}: {}", error.message);
    }
}
