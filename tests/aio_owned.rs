mod support;

#[test]
fn pending_aio_operation_keeps_its_context_borrowed() {
    let scratch = support::Scratch::new("aio-owned-context-borrow");
    let input = scratch.path().join("invalid.lim");
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("library");
    let source = format!(
        "(#import \"{}/linux_x86_64.lim\")
         (#import \"{}/aio_owned.lim\")
         (#fn main () ()
           (#let context-result AioOwnedContextCreate
             (#call aio-owned-context-create (:)))
           (#let-mut context AioOwnedContext
             (#match context-result
               (#case (AioOwnedContextCreated owner) owner)
               (#case (AioOwnedContextCreateFailed error)
                 (#block (#forget error) (#unreachable)))))
           (#let submission AioOwnedSubmit
             (#call aio-owned-poll-submit
               (: context (#borrow context) : fd 0i64 : events 1u16)))
           (#let pending AioOwnedPending
             (#match submission
               (#case (AioOwnedSubmitted operation) operation)
               (#case (AioOwnedSubmitFailed error)
                 (#block (#forget error) (#unreachable)))))
           (#call aio-owned-context-destroy (: context context))
           (#forget pending)
           (#return ()))",
        library.display(),
        library.display()
    );
    let diagnostic = lim::compile_source_to_assembly(
        &source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        diagnostic.message.contains("borrow") || diagnostic.message.contains("consumed"),
        "moving the context before operation completion must be rejected: {diagnostic:?}"
    );
}

#[test]
fn one_aio_context_accepts_multiple_outstanding_operations() {
    let scratch = support::Scratch::new("aio-owned-multiple-in-flight");
    let input = scratch.path().join("multiple.lim");
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("library");
    let source = format!(
        "(#import \"{}/linux_x86_64.lim\")
         (#import \"{}/aio_owned.lim\")
         (#fn main () ()
           (#let context-result AioOwnedContextCreate
             (#call aio-owned-context-create (:)))
           (#let-mut context AioOwnedContext
             (#match context-result
               (#case (AioOwnedContextCreated owner) owner)
               (#case (AioOwnedContextCreateFailed error)
                 (#block (#forget error) (#unreachable)))))
           (#let first-submission AioOwnedSubmit
             (#call aio-owned-poll-submit
               (: context (#borrow context) : fd 0i64 : events 1u16)))
           (#let first-operation AioOwnedPending
             (#match first-submission
               (#case (AioOwnedSubmitted operation) operation)
               (#case (AioOwnedSubmitFailed error)
                 (#block (#forget error) (#unreachable)))))
           (#let second-submission AioOwnedSubmit
             (#call aio-owned-poll-submit
               (: context (#borrow context) : fd 0i64 : events 1u16)))
           (#forget second-submission)
           (#forget first-operation)
           (#let destroyed i64
             (#call aio-owned-context-destroy (: context context)))
           (#forget destroyed)
           (#return ()))",
        library.display(),
        library.display()
    );
    lim::compile_source_to_assembly(
        &source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("two pending requests should be accepted: {error:?}"));
}

#[test]
fn native_aio_wait_routes_another_requests_completion() {
    use std::{process::Command, time::Duration};

    let scratch = support::Scratch::new("aio-owned-completion-routing");
    let input = scratch.path().join("routing.lim");
    let binary = scratch.path().join("routing");
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("library");
    let source = format!(
        r#"(#import "{}/linux_x86_64.lim")
           (#import "{}/aio_owned.lim")
           (#fn main () u64
             (#let context-result AioOwnedContextCreate
               (#call aio-owned-context-create (:)))
             (#let-mut context AioOwnedContext
               (#match context-result
                 (#case (AioOwnedContextCreated owner) owner)
                 (#case (AioOwnedContextCreateFailed error)
                   (#block (#forget error) (#unreachable)))))
             (#let fd-b i64 (#call linux-eventfd2 (: initial-value 0u32 : flags 0i32)))
             (#let fd-a i64 (#call linux-eventfd2 (: initial-value 0u32 : flags 0i32)))
             (#assert (#i64.>= fd-a 0i64))
             (#assert (#i64.>= fd-b 0i64))
             (#let submission-b AioOwnedSubmit
               (#call aio-owned-poll-submit
                 (: context (#borrow context) : fd fd-b : events 1u16)))
             (#let pending-b AioOwnedPending
               (#match submission-b
                 (#case (AioOwnedSubmitted operation) operation)
                 (#case (AioOwnedSubmitFailed error)
                   (#block (#forget error) (#unreachable)))))
             (#let submission-a AioOwnedSubmit
               (#call aio-owned-poll-submit
                 (: context (#borrow context) : fd fd-a : events 1u16)))
             (#let pending-a AioOwnedPending
               (#match submission-a
                 (#case (AioOwnedSubmitted operation) operation)
                 (#case (AioOwnedSubmitFailed error)
                   (#block (#forget error) (#unreachable)))))
             (#let scratch (#ptr-mut u8)
               (#unsafe (#call linux-mmap
                 (: address (#ptr-null (#ptr-mut u8)) : length 4096usize
                  : protection 3u32 : flags 34u32 : fd -1i64 : offset 0i64))))
             (#let value (#ptr-mut u64)
               (#unsafe (#asm (#ptr-mut u64) ((rdi scratch)) "lea rax, [rdi+256]")))
             (#unsafe (#ptr-write value 1u64))
             (#let bytes (#ptr-mut u8)
               (#unsafe (#asm (#ptr-mut u8) ((rdi scratch)) "lea rax, [rdi+256]")))
             (#assert (#i64.==
               (#unsafe (#call linux-write (: fd fd-b : source bytes : count 8usize)))
               8i64))
             (#let delay LinuxTimespec
               (#struct-literal LinuxTimespec ((seconds 0i64) (nanoseconds 10000000i64))))
             (#let-mut remaining LinuxTimespec
               (#struct-literal LinuxTimespec ((seconds 0i64) (nanoseconds 0i64))))
             (#assert (#i64.== (#call linux-nanosleep
               (: request (#borrow delay) : remaining (#borrow-mut remaining))) 0i64))
             (#assert (#i64.==
               (#unsafe (#call linux-write (: fd fd-a : source bytes : count 8usize)))
               8i64))
             (#let wait-a AioOwnedWait (#call aio-owned-wait (: operation pending-a)))
             (#let completed-a AioOwnedCompleted
               (#match wait-a
                 (#case (AioOwnedFinished operation) operation)
                 (#case (AioOwnedWaitFailed failure)
                   (#block
                     (#let (#tuple still-pending error)
                       (#tuple AioOwnedPending i64) failure)
                     (#forget still-pending)
                     (#forget error)
                     (#unreachable)))))
             (#let wait-b AioOwnedWait (#call aio-owned-wait (: operation pending-b)))
             (#let completed-b AioOwnedCompleted
               (#match wait-b
                 (#case (AioOwnedFinished operation) operation)
                 (#case (AioOwnedWaitFailed failure)
                   (#block
                     (#let (#tuple still-pending error)
                       (#tuple AioOwnedPending i64) failure)
                     (#forget still-pending)
                     (#forget error)
                     (#unreachable)))))
             (#assert (#i64.== (#call aio-owned-completed-result
               (: operation (#borrow completed-a))) 1i64))
             (#assert (#i64.== (#call aio-owned-completed-result
               (: operation (#borrow completed-b))) 1i64))
             (#assert (#i64.== (#call aio-owned-completed-destroy
               (: operation completed-a)) 0i64))
             (#assert (#i64.== (#call aio-owned-completed-destroy
               (: operation completed-b)) 0i64))
             (#assert (#i64.== (#call aio-owned-context-destroy
               (: context context)) 0i64))
             (#assert (#i64.== (#call linux-close (: fd fd-a)) 0i64))
             (#assert (#i64.== (#call linux-close (: fd fd-b)) 0i64))
             (#assert (#i64.== (#unsafe (#call linux-munmap
               (: address scratch : length 4096usize))) 0i64))
             (#return 42u64))"#,
        library.display(),
        library.display()
    );
    std::fs::write(&input, source).unwrap();
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("compile completion-routing test");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, _, stderr) = support::run(&mut Command::new(binary), Duration::from_secs(5), 1024)
        .expect("run completion-routing test");
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}
