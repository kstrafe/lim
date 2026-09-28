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
