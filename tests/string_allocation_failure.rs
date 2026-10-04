use std::{fs, process::Command, time::Duration};

mod support;

fn allocator_with_calls(replacements: &[(&str, &str)]) -> String {
    fn collect(
        node: &lim::SpannedExpr,
        replacements: &[(&str, &str)],
        edits: &mut Vec<(lim::Span, String)>,
    ) {
        if matches!(node.children.first().map(|child| &child.expr),
            Some(lim::Expr::Symbol(head)) if head == "#call")
        {
            let callee = &node.children[1];
            if let lim::Expr::Symbol(name) = &callee.expr {
                for (old, new) in replacements {
                    if name == old {
                        edits.push((callee.span, new.to_string()));
                    }
                }
            }
        }
        for child in &node.children {
            collect(child, replacements, edits);
        }
    }
    let mut source = include_str!("../library/system_allocator.lim").to_owned();
    let mut edits = Vec::new();
    for node in lim::parse(&source).unwrap() {
        collect(&node, replacements, &mut edits);
    }
    assert_eq!(edits.len(), replacements.len());
    edits.sort_by_key(|(span, _)| span.start);
    for (span, new) in edits.into_iter().rev() {
        source.replace_range(span.start..span.end, &new);
    }
    source
}

// Substitute only allocator calls in a scratch copy of the actual library.
// This exercises its real error branches without huge allocations or relying
// on platform overcommit policy. The real malloc/free still own successful
// allocations; a failing realloc must not release or mutate the original.
fn execute(allocator: &str, body: &str, label: &str) {
    let scratch = support::Scratch::new(label);
    fs::write(scratch.path().join("system_allocator.lim"), allocator).unwrap();
    fs::write(
        scratch.path().join("string.lim"),
        include_str!("../library/string.lim"),
    )
    .unwrap();
    let source = format!("(#import \"string.lim\")\n{body}");
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
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
    assert_eq!(status.code(), Some(42), "{status:?}: {stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn allocation_failures_are_explicit_and_empty_owners_need_no_allocation() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[("malloc", "failing-malloc"), ("free", "unexpected-free")]),
        "(#fn failing-malloc (: size usize) (#ptr-mut u8)
           (#return (#ptr-null (#ptr-mut u8))))
         (#fn unexpected-free (: pointer (#ptr-mut u8)) ()
           (#panic) (#return ()))"
    );
    execute(
        &allocator,
        r#"(#fn main () u64
          (#let-mut empty String (#call String-new ()))
          (#assert (#call String-is-empty (: string (#borrow empty))))
          (#assert (#usize.== (#call String-capacity (: string (#borrow empty))) 0usize))
          (#assert (#match (#call String-reserve (: string (#borrow-mut empty) : additional 0usize))
            (#case StringOk true) (#case (StringErr error) false)))
          (#assert (#match (#call String-reserve (: string (#borrow-mut empty) : additional 1usize))
            (#case (StringErr StringOutOfMemory) true) (#case _ false)))
          (#assert (#usize.== (#call String-capacity (: string (#borrow empty))) 0usize))
          (#call String-free (: string empty))
          (#assert (#match (#call String-with-capacity (: capacity 1usize))
            (#case (StringCreateFailed error) (#match error (#case StringOutOfMemory true) (#case _ false)))
            (#case (StringCreated unexpected) (#block (#call String-free (: string unexpected)) false))))
          (#let text (#array char 1) "a")
          (#assert (#match (#call String-from-chars (: text (#slice-of (#borrow text))))
            (#case (StringCreateFailed error) (#match error (#case StringOutOfMemory true) (#case _ false)))
            (#case (StringCreated unexpected) (#block (#call String-free (: string unexpected)) false))))
          (#assert (#match (#call String-with-capacity (: capacity 0usize))
            (#case (StringCreated zero) (#block (#call String-free (: string zero)) true))
            (#case (StringCreateFailed error) false)))
          (#return 42u64))"#,
        "string-failed-malloc",
    );
}

#[test]
fn failed_growth_and_invalid_append_preserve_contents_and_capacity() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[("realloc", "failing-realloc")]),
        "(#fn failing-realloc (: pointer (#ptr-mut u8) : size usize) (#ptr-mut u8)
           (#return (#ptr-null (#ptr-mut u8))))"
    );
    execute(
        &allocator,
        r#"(#fn main () u64
          (#let-mut text String (#call String-new ()))
          (#let prefix (#array char 3) "abc")
          (#assert (#match (#call String-push-chars (: string (#borrow-mut text) : text (#slice-of (#borrow prefix))))
            (#case StringOk true) (#case _ false)))
          (#let capacity usize (#call String-capacity (: string (#borrow text))))
          (#let appended (#array char 9) "123456789")
          (#assert (#match (#call String-push-chars (: string (#borrow-mut text) : text (#slice-of (#borrow appended))))
            (#case (StringErr StringOutOfMemory) true) (#case _ false)))
          (#assert (#match (#call String-reserve (: string (#borrow-mut text) : additional 18446744073709551615usize))
            (#case (StringErr StringCapacityOverflow) true) (#case _ false)))
          (#let invalid (#array u8 2) (#array-of (#array u8 2) 192u8 175u8))
          (#assert (#match (#call String-push-utf8 (: string (#borrow-mut text) : bytes (#slice-of (#borrow invalid))))
            (#case (StringErr StringInvalidUtf8) true) (#case _ false)))
          (#assert (#usize.== (#call String-len (: string (#borrow text))) 3usize))
          (#assert (#usize.== (#call String-capacity (: string (#borrow text))) capacity))
          (#assert (#match (#call String-byte-at (: string (#borrow text) : index 2usize))
            (#case (StringByte byte) (#u8.== byte 99u8)) (#case _ false)))
          (#call String-free (: string text))
          (#return 42u64))"#,
        "string-failed-realloc",
    );
}

#[test]
fn failed_deep_clone_preserves_the_original_owner() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[("malloc", "selective-malloc")]),
        "(#fn selective-malloc (: size usize) (#ptr-mut u8)
           (#return (#if (#usize.== size 8usize)
             (#ptr-null (#ptr-mut u8)) (#unsafe (#call malloc (: size size))))))"
    );
    execute(
        &allocator,
        r#"(#fn main () u64
          (#let-mut text String (#call String-new ()))
          (#assert (#match (#call String-reserve (: string (#borrow-mut text) : additional 16usize))
            (#case StringOk true) (#case _ false)))
          (#assert (#match (#call String-push-char (: string (#borrow-mut text) : value #\é))
            (#case StringOk true) (#case _ false)))
          (#assert (#match (#call String-try-clone (: string (#borrow text)))
            (#case (StringCreateFailed error) (#match error (#case StringOutOfMemory true) (#case _ false)))
            (#case (StringCreated unexpected) (#block (#call String-free (: string unexpected)) false))))
          (#assert (#usize.== (#call String-len (: string (#borrow text))) 2usize))
          (#assert (#usize.== (#call String-capacity (: string (#borrow text))) 16usize))
          (#assert (#match (#call String-pop-char (: string (#borrow-mut text)))
            (#case (StringPopped value) (#char.== value #\é)) (#case _ false)))
          (#call String-free (: string text))
          (#return 42u64))"#,
        "string-failed-clone",
    );
}

#[test]
fn zero_and_oversize_raw_requests_are_rejected_before_libc() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[
            ("malloc", "unexpected-malloc"),
            ("realloc", "unexpected-realloc")
        ]),
        "(#fn unexpected-malloc (: size usize) (#ptr-mut u8)
           (#panic) (#return (#ptr-null (#ptr-mut u8))))
         (#fn unexpected-realloc (: pointer (#ptr-mut u8) : size usize) (#ptr-mut u8)
           (#panic) (#return (#ptr-null (#ptr-mut u8))))"
    );
    execute(
        &allocator,
        r#"(#fn main () u64
          (#assert (#match (#call system-allocate (: size 0usize))
            (#case (SystemAllocationFailed error) (#match error (#case SystemAllocationInvalidSize true) (#case _ false)))
            (#case (SystemAllocated pointer) false)))
          (#assert (#match (#call system-allocate (: size 18446744073709551615usize))
            (#case (SystemAllocationFailed error) (#match error (#case SystemAllocationInvalidSize true) (#case _ false)))
            (#case (SystemAllocated pointer) false)))
          (#assert (#match (#unsafe (#call system-reallocate (: pointer (#ptr-null (#ptr-mut u8)) : size 0usize)))
            (#case (SystemAllocationFailed error) (#match error (#case SystemAllocationInvalidSize true) (#case _ false)))
            (#case (SystemAllocated pointer) false)))
          (#return 42u64))"#,
        "string-allocation-size-validation",
    );
}
