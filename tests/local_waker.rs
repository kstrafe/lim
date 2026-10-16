mod support;

use std::{fs, process::Command, time::Duration};

fn source(body: &str) -> String {
    format!(
        "(#import \"{}/library/local_waker.lim\")
         (#struct WakeExecutor () ((count #u64)))
         (#fn notify ((executor (#ref WakeExecutor)) (metadata (#ref #u64))) ()
           (#return ()))
         (#fn clone-metadata ((metadata (#ref #u64))) #u64
           (#return (#deref metadata)))
         (#fn destroy-metadata ((executor (#ref WakeExecutor)) (metadata #u64)) ()
           (#return ()))
         (@#local-waker
           (LocalWake local-wake-create local-wake local-wake-by-ref
             local-wake-clone local-wake-destroy)
           (WakeExecutor #u64)
           (notify clone-metadata destroy-metadata))
         {body}",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn compile_error(body: &str) -> String {
    let scratch = support::Scratch::new("local-waker-error");
    lim::compile_source_to_assembly(
        &source(body),
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
    .message
}

#[test]
fn generated_local_waker_cannot_outlive_its_executor() {
    let error = compile_error(
        "(#fn escape () LocalWake
           (#let executor WakeExecutor (#struct-literal WakeExecutor ((count 0u64))))
           (#return (#call local-wake-create (: executor (#borrow executor) : metadata 1u64))))
         (#fn main () #u64 (#return 0u64))",
    );
    assert!(
        error.contains("local") || error.contains("outlive"),
        "{error}"
    );
}

#[test]
fn generated_local_waker_is_not_send_even_for_a_sync_executor() {
    let error = compile_error(
        "(#fn worker ((waker LocalWake)) #u64
           (#call local-wake-destroy (: waker waker))
           (#return 0u64))
         (@#thread-spawn (: task WakeWorker : worker worker))
         (#fn main () #u64 (#return 0u64))",
    );
    assert!(error.contains("does not implement Send"), "{error}");
}

#[test]
fn generated_local_waker_is_inspectable_and_reports_shape_errors() {
    let scratch = support::Scratch::new("local-waker-generated");
    let source = include_str!("../examples/local_waker.lim")
        .replace(
            "../library/local_waker.lim",
            &format!("{}/library/local_waker.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/cell.lim",
            &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
        );
    let input = scratch.path().join("main.lim");
    fs::write(&input, source).unwrap();
    let (status, _, error) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(scratch.path().join("program")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&error));
    let generated = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "lim")
        })
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(generated.contains("(#struct CounterWaker ()"));
    assert!(generated.contains("counter-waker-wake-by-ref"));
    assert!(generated.contains("(#ptr #u8)"));

    let error = compile_error("(@#local-waker (Only) (WakeExecutor #u64) (notify clone-metadata destroy-metadata)) (#fn main () #u64 (#return 0u64))");
    assert!(error.contains("names must be"), "{error}");
}
