use std::{fs, process::Command, time::Duration};

mod support;

fn allocator_with_calls(replacements: &[(&str, &str)]) -> String {
    fn collect(
        node: &lim::SpannedExpr,
        replacements: &[(&str, &str)],
        edits: &mut Vec<(lim::Span, String)>,
    ) {
        if matches!(node.children.first().map(|child| &child.expr),
            Some(lim::Expr::Symbol(head)) if matches!(head.as_str(), "#call" | "#unsafe-call"))
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
    for node in lim::parse_source_unit(&source).unwrap() {
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
// on platform overcommit policy. The native allocator owns successful
// allocations; a failing realloc must not release or mutate the original.
fn execute(allocator: &str, body: &str, label: &str) {
    let scratch = support::Scratch::new(label);
    fs::write(scratch.path().join("system_allocator.lim"), allocator).unwrap();
    fs::write(
        scratch.path().join("string.lim"),
        include_str!("../library/string.lim"),
    )
    .unwrap();
    let source = format!("#alias String = ./string.lim::String\n#alias String::byte-at = ./string.lim::String::byte-at\n#alias String::bytes = ./string.lim::String::bytes\n#alias String::capacity = ./string.lim::String::capacity\n#alias String::clear = ./string.lim::String::clear\n#alias String::data-pointer = ./string.lim::String::data-pointer\n#alias String::free = ./string.lim::String::free\n#alias String::from-chars = ./string.lim::String::from-chars\n#alias String::from-utf8 = ./string.lim::String::from-utf8\n#alias String::is-empty = ./string.lim::String::is-empty\n#alias String::len = ./string.lim::String::len\n#alias String::new = ./string.lim::String::new\n#alias String::pop-char = ./string.lim::String::pop-char\n#alias String::push-char = ./string.lim::String::push-char\n#alias String::push-chars = ./string.lim::String::push-chars\n#alias String::push-string = ./string.lim::String::push-string\n#alias String::push-utf8 = ./string.lim::String::push-utf8\n#alias String::reserve = ./string.lim::String::reserve\n#alias String::scalar-width = ./string.lim::String::scalar-width\n#alias String::try-clone = ./string.lim::String::try-clone\n#alias String::utf8-valid = ./string.lim::String::utf8-valid\n#alias String::with-capacity = ./string.lim::String::with-capacity\n#alias String::write-scalar = ./string.lim::String::write-scalar\n#alias StringByteResult = ./string.lim::StringByteResult\n#alias StringBytes = ./string.lim::StringBytes\n#alias StringBytes::byte-at = ./string.lim::StringBytes::byte-at\n#alias StringBytes::len = ./string.lim::StringBytes::len\n#alias StringCreateResult = ./string.lim::StringCreateResult\n#alias StringError = ./string.lim::StringError\n#alias StringPopResult = ./string.lim::StringPopResult\n#alias StringStatus = ./string.lim::StringStatus\n#alias SystemAllocationError = ./system_allocator.lim::SystemAllocationError\n#alias SystemAllocationResult = ./system_allocator.lim::SystemAllocationResult\n#alias SystemAllocator = ./system_allocator.lim::SystemAllocator\n#alias SystemAllocator::Allocator::Allocation = ./system_allocator.lim::SystemAllocator::Allocator::Allocation\n#alias SystemAllocator::Allocator::Error = ./system_allocator.lim::SystemAllocator::Allocator::Error\n#alias SystemAllocator::Allocator::State = ./system_allocator.lim::SystemAllocator::Allocator::State\n#alias SystemAllocator::Allocator::allocate = ./system_allocator.lim::SystemAllocator::Allocator::allocate\n#alias SystemAllocator::Allocator::deallocate = ./system_allocator.lim::SystemAllocator::Allocator::deallocate\n#alias SystemAllocator::Allocator::grow = ./system_allocator.lim::SystemAllocator::Allocator::grow\n#alias system-allocate = ./system_allocator.lim::system-allocate\n#alias system-heap-allocate = ./system_allocator.lim::system-heap-allocate\n#alias system-heap-deallocate = ./system_allocator.lim::system-heap-deallocate\n#alias system-heap-reallocate = ./system_allocator.lim::system-heap-reallocate\n#alias system-reallocate = ./system_allocator.lim::system-reallocate\n{body}");
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
        allocator_with_calls(&[
            ("system-heap-allocate", "failing-allocate"),
            ("system-heap-deallocate", "unexpected-deallocate")
        ]),
        "#fn failing-allocate ((size #usize)) (#ptr-mut #u8)
             (#return (#ptr-null (#ptr-mut #u8)))
#unsafe-fn unexpected-deallocate ((pointer (#ptr-mut #u8))) ()
             (#panic) (#return ())\n"
    );
    execute(
        &allocator,
        r#"#fn main () #u64
            (#let-mut empty String (#call String::new ()))
            (#assert (#call String::is-empty ((string (#borrow empty)))))
            (#assert (#usize::eq (#call String::capacity ((string (#borrow empty)))) 0usize))
            (#assert (#match (#call String::reserve ((string (#borrow-mut empty)) (additional 0usize)))
              (#case StringStatus.StringOk true) (#case (StringStatus.StringErr error) false)))
            (#assert (#match (#call String::reserve ((string (#borrow-mut empty)) (additional 1usize)))
              (#case (StringStatus.StringErr StringError.StringOutOfMemory) true) (#case _ false)))
            (#assert (#usize::eq (#call String::capacity ((string (#borrow empty)))) 0usize))
            (#call String::free ((string empty)))
            (#assert (#match (#call String::with-capacity ((capacity 1usize)))
              (#case (StringCreateResult.StringCreateFailed error) (#match error (#case StringError.StringOutOfMemory true) (#case _ false)))
              (#case (StringCreateResult.StringCreated unexpected) (#block (#call String::free ((string unexpected))) false))))
            (#let text (#array #char 1) "a")
            (#assert (#match (#call String::from-chars ((text (#slice-of (#borrow text)))))
              (#case (StringCreateResult.StringCreateFailed error) (#match error (#case StringError.StringOutOfMemory true) (#case _ false)))
              (#case (StringCreateResult.StringCreated unexpected) (#block (#call String::free ((string unexpected))) false))))
            (#assert (#match (#call String::with-capacity ((capacity 0usize)))
              (#case (StringCreateResult.StringCreated zero) (#block (#call String::free ((string zero))) true))
              (#case (StringCreateResult.StringCreateFailed error) false)))
            (#return 42u64)
"#,
        "string-failed-malloc",
    );
}

#[test]
fn failed_growth_and_invalid_append_preserve_contents_and_capacity() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[("system-heap-reallocate", "failing-reallocate")]),
        "#unsafe-fn failing-reallocate ((pointer (#ptr-mut #u8)) (size #usize)) (#ptr-mut #u8)
             (#return (#ptr-null (#ptr-mut #u8)))\n"
    );
    execute(
        &allocator,
        r#"#fn main () #u64
            (#let-mut text String (#call String::new ()))
            (#let prefix (#array #char 3) "abc")
            (#assert (#match (#call String::push-chars ((string (#borrow-mut text)) (text (#slice-of (#borrow prefix)))))
              (#case StringStatus.StringOk true) (#case _ false)))
            (#let capacity #usize (#call String::capacity ((string (#borrow text)))))
            (#let appended (#array #char 9) "123456789")
            (#assert (#match (#call String::push-chars ((string (#borrow-mut text)) (text (#slice-of (#borrow appended)))))
              (#case (StringStatus.StringErr StringError.StringOutOfMemory) true) (#case _ false)))
            (#assert (#match (#call String::reserve ((string (#borrow-mut text)) (additional 18446744073709551615usize)))
              (#case (StringStatus.StringErr StringError.StringCapacityOverflow) true) (#case _ false)))
            (#let invalid (#array #u8 2) (#array-of (#array #u8 2) 192u8 175u8))
            (#assert (#match (#call String::push-utf8 ((string (#borrow-mut text)) (bytes (#slice-of (#borrow invalid)))))
              (#case (StringStatus.StringErr StringError.StringInvalidUtf8) true) (#case _ false)))
            (#assert (#usize::eq (#call String::len ((string (#borrow text)))) 3usize))
            (#assert (#usize::eq (#call String::capacity ((string (#borrow text)))) capacity))
            (#assert (#match (#call String::byte-at ((string (#borrow text)) (index 2usize)))
              (#case (StringByteResult.StringByte byte) (#u8::eq byte 99u8)) (#case _ false)))
            (#call String::free ((string text)))
            (#return 42u64)
"#,
        "string-failed-realloc",
    );
}

#[test]
fn failed_string_append_preserves_both_owners() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[("system-heap-reallocate", "failing-reallocate")]),
        "#unsafe-fn failing-reallocate ((pointer (#ptr-mut #u8)) (size #usize)) (#ptr-mut #u8)
            (#return (#ptr-null (#ptr-mut #u8)))\n"
    );
    execute(
        &allocator,
        r#"#fn main () #u64
        (#let prefix (#array #char 3) "abc")
        (#let suffix (#array #char 9) "123456789")
        (#let-mut target String (#match (#call String::from-chars ((text (#slice-of (#borrow prefix)))))
          (#case (StringCreateResult.StringCreated created-target) created-target) (#case _ (#panic))))
        (#let source String (#match (#call String::from-chars ((text (#slice-of (#borrow suffix)))))
          (#case (StringCreateResult.StringCreated created-source) created-source) (#case _ (#panic))))
        (#let capacity #usize (#call String::capacity ((string (#borrow target)))))
        (#assert (#match (#call String::push-string ((string (#borrow-mut target)) (text (#borrow source))))
          (#case (StringStatus.StringErr StringError.StringOutOfMemory) true) (#case _ false)))
        (#assert (#usize::eq (#call String::len ((string (#borrow target)))) 3usize))
        (#assert (#usize::eq (#call String::capacity ((string (#borrow target)))) capacity))
        (#assert (#usize::eq (#call String::len ((string (#borrow source)))) 9usize))
        (#assert (#match (#call String::byte-at ((string (#borrow target)) (index 2usize)))
          (#case (StringByteResult.StringByte byte) (#u8::eq byte 99u8)) (#case _ false)))
        (#assert (#match (#call String::byte-at ((string (#borrow source)) (index 8usize)))
          (#case (StringByteResult.StringByte byte) (#u8::eq byte 57u8)) (#case _ false)))
        (#call String::free ((string target))) (#call String::free ((string source)))
        (#return 42u64)
"#,
        "string-failed-string-append",
    );
}

#[test]
fn failed_deep_clone_preserves_the_original_owner() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[("system-heap-allocate", "selective-allocate")]),
        "#fn selective-allocate ((size #usize)) (#ptr-mut #u8)
             (#return (#if (#usize::eq size 8usize)
               (#ptr-null (#ptr-mut #u8)) (#unsafe (#call system-heap-allocate ((size size))))))\n"
    );
    execute(
        &allocator,
        r#"#fn main () #u64
            (#let-mut text String (#call String::new ()))
            (#assert (#match (#call String::reserve ((string (#borrow-mut text)) (additional 16usize)))
              (#case StringStatus.StringOk true) (#case _ false)))
            (#assert (#match (#call String::push-char ((string (#borrow-mut text)) (value #\é)))
              (#case StringStatus.StringOk true) (#case _ false)))
            (#assert (#match (#call String::try-clone ((string (#borrow text))))
              (#case (StringCreateResult.StringCreateFailed error) (#match error (#case StringError.StringOutOfMemory true) (#case _ false)))
              (#case (StringCreateResult.StringCreated unexpected) (#block (#call String::free ((string unexpected))) false))))
            (#assert (#usize::eq (#call String::len ((string (#borrow text)))) 2usize))
            (#assert (#usize::eq (#call String::capacity ((string (#borrow text)))) 16usize))
            (#assert (#match (#call String::pop-char ((string (#borrow-mut text))))
              (#case (StringPopResult.StringPopped value) (#char::eq value #\é)) (#case _ false)))
            (#call String::free ((string text)))
            (#return 42u64)
"#,
        "string-failed-clone",
    );
}

#[test]
fn zero_and_oversize_raw_requests_are_rejected_before_allocator_hooks() {
    let allocator = format!(
        "{}\n{}",
        allocator_with_calls(&[
            ("system-heap-allocate", "unexpected-allocate"),
            ("system-heap-reallocate", "unexpected-reallocate")
        ]),
        "#fn unexpected-allocate ((size #usize)) (#ptr-mut #u8)
             (#panic) (#return (#ptr-null (#ptr-mut #u8)))
#unsafe-fn unexpected-reallocate ((pointer (#ptr-mut #u8)) (size #usize)) (#ptr-mut #u8)
             (#panic) (#return (#ptr-null (#ptr-mut #u8)))\n"
    );
    execute(
        &allocator,
        r#"#fn main () #u64
            (#assert (#match (#call system-allocate ((size 0usize)))
              (#case (SystemAllocationResult.SystemAllocationFailed error) (#match error (#case SystemAllocationError.SystemAllocationInvalidSize true) (#case _ false)))
              (#case (SystemAllocationResult.SystemAllocated pointer) false)))
            (#assert (#match (#call system-allocate ((size 18446744073709551615usize)))
              (#case (SystemAllocationResult.SystemAllocationFailed error) (#match error (#case SystemAllocationError.SystemAllocationInvalidSize true) (#case _ false)))
              (#case (SystemAllocationResult.SystemAllocated pointer) false)))
            (#assert (#match (#unsafe (#unsafe-call system-reallocate ((pointer (#ptr-null (#ptr-mut #u8))) (size 0usize))))
              (#case (SystemAllocationResult.SystemAllocationFailed error) (#match error (#case SystemAllocationError.SystemAllocationInvalidSize true) (#case _ false)))
              (#case (SystemAllocationResult.SystemAllocated pointer) false)))
            (#return 42u64)
"#,
        "string-allocation-size-validation",
    );
}
