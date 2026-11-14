mod support;

use std::{fs, process::Command, time::Duration};

fn fixture() -> String {
    include_str!("fixtures/pin_box_arena.lim").replace(
        "../../library/",
        &format!("{}/library/", env!("CARGO_MANIFEST_DIR")),
    )
}

fn check(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("allocator-bundle-check");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("allocator-bundle-run");
    let input = scratch.path().join("main.lim");
    let output = scratch.path().join("program");
    fs::write(
        &input,
        source.replace(
            "../library/",
            &format!("{}/library/", env!("CARGO_MANIFEST_DIR")),
        ),
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(input)
            .arg("-o")
            .arg(&output),
        Duration::from_secs(30),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) = support::run(
        &mut Command::new(output),
        Duration::from_secs(5),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(expected),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn handwritten_bundle_aliases_preserve_failure_and_need_no_grow() {
    let source = fixture();
    assert!(!source.contains("::grow"));
    run(&source, 42);
}

#[test]
fn generated_provider_needs_no_special_producer() {
    let source = fixture();
    let nodes = lim::parse(&source).unwrap();
    let mut body = String::new();
    let mut provider = String::new();
    let mut cursor = 0;
    for node in nodes {
        let is_provider = matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.get(1), Some(lim::Expr::Symbol(name))
                if name.starts_with("Arena::Allocator::")));
        if is_provider {
            body.push_str(&source[cursor..node.span.start]);
            provider.push_str(&source[node.span.start..node.span.end]);
            provider.push('\n');
            cursor = node.span.end;
        }
    }
    body.push_str(&source[cursor..]);
    run(
        &format!("(#gn provide () `({provider}))\n(#generate provide)\n{body}"),
        42,
    );
}

#[test]
fn missing_deallocation_and_wrong_allocate_signature_are_rejected() {
    for (source, operation) in [
        (fixture().replace("(#unsafe-fn Arena::Allocator::deallocate", "(#unsafe-fn unused-deallocate"), "deallocate"),
        (fixture().replace(
            "((allocator (#ref Arena)) (layout #usize) (alignment #usize)) Arena::Allocator::Allocation",
            "((allocator (#ref Arena)) (layout #usize) (alignment #u64)) Arena::Allocator::Allocation",
        ), "alignment"),
    ] {
        let error = check(&source).expect_err("invalid bundle must be rejected");
        assert!(error.message.contains(operation), "{error:?}");
    }
}

#[test]
fn bundle_success_payload_must_be_a_byte_pointer() {
    for source in [
        fixture().replace("(#ptr-mut #u8)", "(#ptr-mut #u64)"),
        fixture()
            .replace(
                "(Arena::Allocator::Allocation.Allocated (#ptr-mut #u8))",
                "(Arena::Allocator::Allocation.Allocated #usize)",
            )
            .replace(
                "(Arena::Allocator::Allocation.Allocated pointer)",
                "(Arena::Allocator::Allocation.Allocated (#ptr-address pointer))",
            ),
    ] {
        let error =
            check(&source).expect_err("success payload must match the byte ABI before casting");
        assert!(error.message.contains("type"), "{error:?}");
    }
}

#[test]
fn vector_bundle_requires_grow() {
    let source = include_str!("../examples/vec_allocator.lim")
        .replace(
            "../library/",
            &format!("{}/library/", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "(#unsafe-fn CountingAllocator::Allocator::grow",
            "(#unsafe-fn unused-grow",
        );
    let error = check(&source).expect_err("vector growth requires its bundle operation");
    assert!(
        error.message.contains("CountingAllocator::Allocator::grow"),
        "{error:?}"
    );
}

#[test]
fn allocation_must_be_safe_and_unsafe_operations_require_unsafe_calls() {
    let error = check(&fixture().replace(
        "(#fn Arena::Allocator::allocate",
        "(#unsafe-fn Arena::Allocator::allocate",
    ))
    .expect_err("consumer calls allocate safely");
    assert!(error.message.contains("unsafe"), "{error:?}");

    for operation in ["grow", "deallocate"] {
        let extra = if operation == "grow" {
            "(old-layout 8usize)"
        } else {
            ""
        };
        for call in ["#call", "#unsafe-call"] {
            let expression = format!(
                "({call} SystemAllocator::Allocator::{operation}
                ((allocator (#borrow allocator)) (pointer (#ptr-null (#ptr-mut #u8))
                 {extra}) (layout 16usize) (alignment 8usize)))"
            );
            // Even an unsafe block cannot turn #call into #unsafe-call.
            let expression = if call == "#call" {
                format!("(#unsafe {expression})")
            } else {
                expression
            };
            let source = format!(
                "(#std) (#fn main () #u64
                (#let allocator SystemAllocator (#struct-literal SystemAllocator ()))
                {expression} (#return 42u64))"
            );
            let error = check(&source).expect_err("unsafe call contract must be enforced");
            assert!(error.message.contains("unsafe"), "{error:?}");
        }
    }
}

#[test]
fn bundle_state_alias_does_not_extend_allocator_lifetime() {
    let source = fixture().replace(
        "(#fn main () #u64",
        "(#fn escape () PinU64Box
          (#let arena Arena (#struct-literal Arena ((identity 1u64) (fail false))))
          (#return (#match (#call PinU64Box::create ((allocator (#borrow arena)) (value 42u64)))
            (#case (PinU64Box::CreateResult.Created owner) owner)
            (#case (PinU64Box::CreateResult.Allocation-failed failure) (#block (#forget failure) (#unreachable))))))
        (#fn main () #u64",
    );
    let error = check(&source).expect_err("owner must not escape local state");
    assert!(
        error.message.contains("arena") || error.message.contains("local"),
        "{error:?}"
    );
}

#[test]
fn failed_vector_growth_preserves_initialized_bytes_and_destruction() {
    let source = include_str!("../examples/vec_allocator.lim");
    let start = source
        .find("(#unsafe-fn CountingAllocator::Allocator::grow")
        .unwrap();
    let end = source
        .find("(#unsafe-fn CountingAllocator::Allocator::deallocate")
        .unwrap();
    let source = format!(
        "{}\n(#unsafe-fn CountingAllocator::Allocator::grow
      ((allocator (#ref CountingAllocator)) (pointer (#ptr-mut #u8))
       (old-layout #usize) (layout #usize) (alignment #usize))
      CountingAllocator::Allocator::Allocation
      (#return (CountingAllocator::Allocator::Allocation.AllocationFailed SystemAllocationError.SystemAllocationOutOfMemory)))\n{}",
        &source[..start],
        &source[end..]
    );
    let source = source.replace(
        "  (#let first VecU64::PushResult",
        "  (#let reserved VecU64::ReserveResult (#call VecU64::reserve ((vector (#borrow-mut vector)) (requested 4usize))))
           (#forget reserved)
           (#let first VecU64::PushResult",
    );
    let source = source.replace(
        "  (#call VecU64::sort",
        "  (#let before #usize (#call VecU64::capacity ((vector (#borrow vector)))))
          (#let failure VecU64::ReserveResult
            (#call VecU64::reserve ((vector (#borrow-mut vector)) (requested 1024usize))))
          (#assert (#match failure
            (#case (VecU64::ReserveResult.Err error) (#block (#forget error) true))
            (#case (VecU64::ReserveResult.Ok value) (#block (#forget value) false))))
          (#assert (#usize::eq before (#call VecU64::capacity ((vector (#borrow vector))))))
          (#call VecU64::sort",
    );
    run(&source, 4);
}

#[test]
fn standard_bundle_runs_registered_box() {
    run(include_str!("../examples/future_registration_box.lim"), 42);
}

#[test]
fn native_heap_counting_bundle_preserves_destruction_counts() {
    run(include_str!("../examples/vec_allocator.lim"), 4);
}

#[test]
fn one_bundle_adapts_multiple_types_and_rejects_unknown_operations_or_options() {
    check(
        "(#std)
      (#generate #allocator-for ((allocator SystemAllocator::Allocator) (type #u8)
        (name ByteAllocator) (operations (allocate grow deallocate))))
      (#generate #allocator-for ((allocator SystemAllocator::Allocator) (type #u128)
        (name WideAllocator) (operations (allocate deallocate))))
      (#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
    for (extra, operations, message) in [
        ("", "(allocate destroy)", "unknown operation"),
        ("(surprise true)", "(allocate deallocate)", "unknown"),
    ] {
        let source = format!(
            "(#std)
          (#generate #allocator-for ((allocator SystemAllocator::Allocator) (type #u64)
            (name TypedAllocator) (operations {operations} {extra})))"
        );
        let error = check(&source).expect_err("invalid adapter options must fail expansion");
        assert_eq!(error.code_string(), "E3000");
        assert!(error.message.contains(message), "{error:?}");
        assert!(error.span.is_some(), "{error:?}");
    }
}

#[test]
fn system_bundle_rejects_unsupported_alignment_without_losing_storage() {
    run(
        "(#std)
        (#fn main () #u64
          (#let allocator SystemAllocator (#struct-literal SystemAllocator ()))
          (#assert (#match (#call SystemAllocator::Allocator::allocate
            ((allocator (#borrow allocator)) (layout 16usize) (alignment 3usize)))
            (#case (SystemAllocator::Allocator::Allocation.AllocationFailed error)
              (#match error (#case SystemAllocationError.SystemAllocationInvalidSize true) (#case _ false)))
            (#case (SystemAllocator::Allocator::Allocation.Allocated unexpected)
              (#block (#unsafe (#unsafe-call system-deallocate ((pointer unexpected)))) false))))
          (#return (#match (#call SystemAllocator::Allocator::allocate
            ((allocator (#borrow allocator)) (layout 16usize) (alignment 8usize)))
            (#case (SystemAllocator::Allocator::Allocation.AllocationFailed error)
              (#block (#forget error) 0u64))
            (#case (SystemAllocator::Allocator::Allocation.Allocated pointer)
              (#block
                (#unsafe (#ptr-write pointer 42u8))
                (#assert (#match (#unsafe (#unsafe-call SystemAllocator::Allocator::grow
                  ((allocator (#borrow allocator)) (pointer pointer) (old-layout 16usize)
                   (layout 32usize) (alignment 32usize))))
                  (#case (SystemAllocator::Allocator::Allocation.AllocationFailed error)
                    (#match error (#case SystemAllocationError.SystemAllocationInvalidSize true) (#case _ false)))
                  (#case (SystemAllocator::Allocator::Allocation.Allocated unexpected)
                    (#block (#forget unexpected) false))))
                (#let answer #u8 (#unsafe (#ptr-read pointer)))
                (#unsafe (#unsafe-call SystemAllocator::Allocator::deallocate
                  ((allocator (#borrow allocator)) (pointer pointer) (layout 16usize) (alignment 8usize))))
                (#as answer #u64))))))",
        42,
    );
}
