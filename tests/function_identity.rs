mod support;

use std::{fs, process::Command, time::Duration};

const PROGRAM: &str = r#"
#fn panic ((value (#ref #u64))) #u64 (#return (#deref value))
#fn unreachable ((value #u64)) #u64 (#return value)
#fn borrow ((value #u64)) #u64 (#return value)
#fn clone ((value #u64)) #u64 (#return value)
#fn forget ((value #u64)) #u64 (#return value)
#fn pin-read ((value #u64)) #u64 (#return value)
#fn u64-add-wrap ((left #u64) (right #u64)) #u64 (#return left)
#fn u64-lt ((left #u64) (right #u64)) #bool (#return true)
#fn main () #u64
    (#let value #u64 42u64)
    (#assert (#u64::eq (#call panic ((value (#borrow value)))) 42u64))
    (#assert (#u64::eq (#call unreachable ((value 42u64))) 42u64))
    (#assert (#u64::eq (#call borrow ((value 42u64))) 42u64))
    (#assert (#u64::eq (#call clone ((value 42u64))) 42u64))
    (#assert (#u64::eq (#call forget ((value 42u64))) 42u64))
    (#assert (#u64::eq (#call pin-read ((value 42u64))) 42u64))
    (#assert (#u64::eq (#call u64-add-wrap ((left 42u64) (right 99u64))) 42u64))
    (#assert (#call u64-lt ((left 99u64) (right 42u64))))
    (#assert (#bool::not (#u64::lt 99u64 42u64)))
    (#let copied #u64 (#clone value))
    (#forget copied)
    (#if false (#panic) ())
    (#if false (#unreachable) ())
    (#return (#u64::add-wrap value 0u64))
"#;

fn assert_runs(binary: &std::path::Path) {
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn native_user_function_names_keep_identity_under_call() {
    let scratch = support::Scratch::new("function-identity-native");
    let source = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&source, PROGRAM).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert_runs(&binary);
}

#[test]
fn api_generator_emission_and_reused_cache_preserve_function_identity() {
    let scratch = support::Scratch::new("function-identity-api-cache");
    let source = scratch.path().join("main.lim");
    let text = PROGRAM
        .replace(
            "#fn panic ((value (#ref #u64))) #u64 (#return (#deref value))\n",
            "",
        )
        .replace(
            "#fn main () #u64",
            "(#gn-fn emit-identity () `((#fn panic ((value (#ref #u64))) #u64 (#return (#deref value)))))\n(#gn make-identity () (#gn-call emit-identity))\n(#generate make-identity)\n(#fn main () #u64",
        );
    let cache = scratch.path().join("cache");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let mut assembly = String::new();
    for _ in 0..2 {
        let next = lim::compile_source_to_assembly(
            &text,
            &source,
            &lim::CompileConfig::default(),
            &cache,
            target,
        )
        .unwrap();
        if assembly.is_empty() {
            assembly = next.clone();
        } else {
            assert_eq!(assembly, next, "warm cache changed native output");
        }
    }
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    assert_runs(&binary);
}

#[test]
fn named_arguments_keep_written_evaluation_order_for_colliding_identity() {
    let scratch = support::Scratch::new("function-identity-order");
    let source = "
#fn next ((counter (#ref-mut #u64)) (value #u64)) #u64
          (#assert (#u64::eq (#deref counter) value))
          (#deref-set counter (#u64::add-wrap (#deref counter) 1u64)) (#return value)
#fn panic ((a #u64) (b #u64)) #u64
          (#assert (#u64::eq a 1u64)) (#assert (#u64::eq b 0u64)) (#return 42u64)
#fn main () #u64
          (#let-mut counter #u64 0u64)
          (#let result #u64 (#call panic
            ((b (#call next ((counter (#borrow-mut counter)) (value 0u64))))
             (a (#call next ((counter (#borrow-mut counter)) (value 1u64)))))))
          (#return result)\n";
    let path = scratch.path().join("main.lim");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        source,
        &path,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    assert_runs(&binary);
}

#[test]
fn builtin_pin_read_still_requires_unsafe_when_user_function_shares_its_name() {
    let scratch = support::Scratch::new("function-identity-pin-read-safety");
    let source = "#fn pin-read ((value #u64)) #u64 (#return value)
#fn main () #u64
          (#let-mut owner #u64 1u64)
          (#let pinned (#pin-ref-mut #u64) (#pin-borrow-mut owner))
          (#let value #u64 (#pin-read pinned))\n          (#drop pinned) (#return value)\n";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("unsafe operation"), "{error:?}");
}

#[test]
fn user_panic_argument_type_error_points_at_the_rhs() {
    let scratch = support::Scratch::new("function-identity-panic-type");
    let source = "#fn panic ((value (#ref #u64))) #u64 (#return (#deref value))
#fn main () #u64
          (#return (#call panic ((value true))))\n";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    let span = error
        .span
        .expect("argument type error should carry a source span");
    assert_eq!(&source[span.start..span.end], "true");
}

fn compile_error(source: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new("function-identity-error");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

#[test]
fn user_trap_names_do_not_supply_divergence_or_hide_linear_cleanup() {
    for name in ["panic", "unreachable"] {
        let error = compile_error(&format!(
            "#fn {name} () () (#return ())
#fn main () #u64 (#call {name} ())\n"
        ));
        assert!(error.message.contains("return"), "{error:?}");
        let error = compile_error(&format!(
            "#struct Resource (#linear) ((value #u64))
#fn {name} () () (#return ())
#fn main () #u64
                 (#let owner Resource (#struct-literal Resource ((value 42u64))))
                 (#call {name} ()) (#return 42u64)\n"
        ));
        assert!(error.message.contains("consumed"), "{error:?}");
    }
}

#[test]
fn user_clone_consumes_linear_arguments_instead_of_copying() {
    let source = "#struct Resource (#linear) ((value #u64))
#fn clone ((value Resource)) Resource (#return value)
#fn main () #u64
          (#let owner Resource (#struct-literal Resource ((value 42u64))))
          (#let duplicate Resource (#call clone ((value owner))))
          (#forget duplicate) (#forget owner) (#return 42u64)\n";
    let error = compile_error(source);
    assert!(error.message.contains("consumed"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "owner");
}

#[test]
fn colliding_user_function_recursion_is_still_rejected() {
    let error = compile_error("#fn panic () #u64 (#return (#call panic ()))\n");
    assert!(error.message.contains("recurs"), "{error:?}");
}

#[test]
fn colliding_call_chain_keeps_the_static_stack_depth() {
    let scratch = support::Scratch::new("function-identity-depth");
    let source = "#fn forget () #u64 (#return 42u64)
#fn unreachable () #u64 (#return (#call forget ()))
#fn panic () #u64 (#return (#call unreachable ()))
#fn main () #u64 (#if false (#panic) ()) (#return (#call panic ()))\n";
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let main = assembly.split(".globl main").nth(1).unwrap();
    assert!(main.contains("# lim max call depth: 4"), "{main}");
}

#[test]
fn user_forget_return_keeps_the_referent_borrowed() {
    let source = "#fn forget ((value (#ref #u64))) (#ref #u64) (#return value)
#fn main () #u64
          (#let-mut owner #u64 42u64)
          (#let view (#ref #u64) (#call forget ((value (#borrow owner)))))
          (#set owner 0u64)
          (#return (#deref view))\n";
    let error = compile_error(source);
    assert!(error.message.contains("borrow"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#set");
}

#[test]
fn unsafe_user_borrow_does_not_make_builtin_borrow_unsafe() {
    let scratch = support::Scratch::new("function-identity-unsafe");
    let source = "#unsafe-fn borrow ((value #u64)) #u64 (#return value)
#fn main () #u64
          (#let owner #u64 42u64)
          (#let view (#ref #u64) (#borrow owner))
          (#return (#deref view))\n";
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let unsafe_call = source.replace(
        "(#deref view)",
        "(#unsafe-call borrow ((value (#deref view))))",
    );
    let error = compile_error(&unsafe_call);
    assert!(
        error.message.contains("unsafe function 'borrow'"),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(&unsafe_call[span.start..span.end], "borrow");
}

#[test]
fn external_import_prefixes_colliding_function_and_argument_names() {
    let scratch = support::Scratch::new("function-identity-import");
    fs::write(
        scratch.path().join("library.lim"),
        "#fn panic ((clone #u64)) #u64 (#return clone)\n",
    )
    .unwrap();
    let source = "#alias ext@panic = ./library.lim::panic
#fn main () #u64 (#return (#call ext@panic ((clone 42u64))))\n";
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    assert_runs(&binary);
}

#[test]
fn colliding_calls_keep_aggregate_abi_and_eager_boolean_arguments() {
    let scratch = support::Scratch::new("function-identity-aggregate-eager");
    let source = "
#fn clone () (#array #u64 8)
          (#return (#array-of (#array #u64 8) 42u64 1u64 2u64 3u64 4u64 5u64 6u64 7u64))
#fn bool-and ((left #bool) (right #bool)) #bool (#return right)
#fn effect ((counter (#ref-mut #u64))) #bool
          (#deref-set counter 42u64) (#return true)
#fn main () #u64
          (#let values (#array #u64 8) (#call clone ()))
          (#let-mut counter #u64 0u64)
          (#assert (#call bool-and ((left false) (right (#call effect ((counter (#borrow-mut counter))))))))
          (#assert (#u64::eq counter 42u64))
          (#return (#index values 0u64))\n";
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    assert_runs(&binary);
}
