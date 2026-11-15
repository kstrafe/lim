mod support;

use std::{fs, process::Command, time::Duration};

fn source(body: &str) -> String {
    format!(
        "#alias lim-gen-local-waker = \"{0}/library/local_waker.lim::#local-waker\"\n#struct WakeExecutor () ((count #u64))\n#fn notify {{\n  #params = ((executor (#ref WakeExecutor)) (metadata (#ref #u64)));\n  #returns = ();\n  #body = (\n             (#return ())\n  );\n}}\n#fn clone-metadata {{\n  #params = ((metadata (#ref #u64)));\n  #returns = #u64;\n  #body = (\n             (#return (#deref metadata))\n  );\n}}\n#fn destroy-metadata {{\n  #params = ((executor (#ref WakeExecutor)) (metadata #u64));\n  #returns = ();\n  #body = (\n             (#return ())\n  );\n}}\n#generate lim-gen-local-waker\n             (LocalWake local-wake-create local-wake local-wake-by-ref\n               local-wake-clone local-wake-destroy)\n             (WakeExecutor #u64)\n             (notify clone-metadata destroy-metadata)\n{body}",
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
        "#fn escape {
  #params = ();
  #returns = LocalWake;
  #body = (
             (#let executor WakeExecutor (#struct-literal WakeExecutor ((count 0u64))))
             (#return (#call local-wake-create ((executor (#borrow executor)) (metadata 1u64))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 0u64)\n  );\n}\n",
    );
    assert!(
        error.contains("local") || error.contains("outlive"),
        "{error}"
    );
}

#[test]
fn generated_local_waker_is_not_send_even_for_a_sync_executor() {
    let error = compile_error(
        "#fn worker {
  #params = ((waker LocalWake));
  #returns = #u64;
  #body = (
             (#call local-wake-destroy ((waker waker)))
             (#return 0u64)
  );
}
#generate #thread-spawn ((task WakeWorker) (worker worker))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 0u64)\n  );\n}\n",
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
    assert!(lim::parse_source_unit(&generated).unwrap().iter().any(|form| {
        matches!(&form.expr, lim::Expr::List(items)
            if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#struct")
                && matches!(items.get(1), Some(lim::Expr::Symbol(name))
                    if name.split_once(".lim::").map_or(name.as_str(), |(_, local)| local) == "CounterWaker")
                && matches!(items.get(2), Some(lim::Expr::List(properties))
                    if matches!(properties.as_slice(), [lim::Expr::Symbol(property)] if property == "#linear")))
    }), "{generated}");
    assert!(generated.contains("counter-waker-wake-by-ref"));
    assert!(generated.contains("(#ptr #u8)"));

    let error = compile_error("#generate lim-gen-local-waker (Pipeline.Only) (WakeExecutor #u64) (notify clone-metadata destroy-metadata)\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n");
    assert!(error.contains("names must be"), "{error}");
}
