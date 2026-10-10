mod support;

use std::process::Command;

#[test]
fn wake_token_table_reports_invalid_busy_and_exhausted_slots() {
    let source = format!(
        "(#import \"{}/library/wake_tokens.lim\")
         (#fn main () #u64
           (#let-mut table WakeTable4 (#call wake-table4-create (:)))
           (#let invalid WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut table) : slot 4usize)))
           (#let invalid-ok #bool (#match invalid
             (#case WakeInvalid4 true) (#case _ false)))
           (#let first WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut table) : slot 1usize)))
           (#let token WakeToken4 (#match first
             (#case (WakeRegistered4 value) value)
             (#case _ (#unreachable))))
           (#let busy WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut table) : slot 1usize)))
           (#let busy-ok #bool (#match busy
             (#case WakeBusy4 true) (#case _ false)))
           (#let retired WakeRetire4
             (#call wake-table4-retire (: table (#borrow-mut table) : token token)))
           (#let retired-ok #bool (#match retired
             (#case WakeRetired4 true) (#case WakeStale4 false)))
           (#let-mut exhausted-table WakeTable4
             (#call wake-table4-create-exhausted (:)))
           (#let exhausted WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut exhausted-table) : slot 1usize)))
           (#let exhausted-ok #bool (#match exhausted
             (#case WakeExhausted4 true) (#case _ false)))
           (#forget table) (#forget exhausted-table)
           (#return (#if
             (#bool.&& invalid-ok
               (#bool.&& busy-ok (#bool.&& retired-ok exhausted-ok)))
             42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let scratch = support::Scratch::new("wake-tokens");
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}

#[test]
fn wake_authority_is_private_to_its_module() {
    let scratch = support::Scratch::new("wake-authority-private");
    for (name, body, expected) in [
        (
            "forge-token",
            "(#fn main () #u64
               (#let token WakeToken4 (#struct-literal WakeToken4
                 ((slot 0usize) (generation 1u64))))
               (#return 0u64))",
            "cannot construct opaque type 'WakeToken4'",
        ),
        (
            "forge-global",
            "(#const TOKEN WakeToken4 (#struct-literal WakeToken4
               ((slot 0usize) (generation 1u64))))
             (#fn main () #u64 (#return 0u64))",
            "cannot construct opaque type 'WakeToken4'",
        ),
        (
            "read-field",
            "(#fn inspect ((token WakeToken4)) #usize
               (#return (#get token slot)))
             (#fn main () #u64 (#return 0u64))",
            "cannot access fields of opaque type 'WakeToken4'",
        ),
        (
            "replace-generations",
            "(#fn main () #u64
               (#let-mut table WakeTable4 (#call wake-table4-create (:)))
               (#set-field table generations (#array-repeat 1u64))
               (#forget table)
               (#return 0u64))",
            "cannot mutate fields of opaque type 'WakeTable4'",
        ),
        (
            "clone-authority",
            "(#fn main () #u64
               (#let table WakeTable4 (#call wake-table4-create (:)))
               (#let duplicate WakeTable4 (#clone table))
               (#forget duplicate)
               (#forget table)
               (#return 0u64))",
            "cannot clone opaque type 'WakeTable4'",
        ),
    ] {
        let source = format!(
            "(#import \"{}/library/wake_tokens.lim\")\n{body}",
            env!("CARGO_MANIFEST_DIR")
        );
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join(format!("{name}.lim")),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.message.contains(expected), "{name}: {error:?}");
        assert_eq!(error.span.expect("private access source span").source_id, 0);
    }
}

#[test]
fn external_import_prefix_does_not_remove_opacity() {
    let scratch = support::Scratch::new("wake-authority-external");
    let source = format!(
        "(#import-external \"{}/library/wake_tokens.lim\" ext-)
         (#fn main () #u64
           (#let token ext-WakeToken4 (#struct-literal ext-WakeToken4
             ((ext-slot 0usize) (ext-generation 1u64))))
           (#return 0u64))",
        env!("CARGO_MANIFEST_DIR")
    );
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("cannot construct opaque type 'ext-WakeToken4'"),
        "{error:?}"
    );
}

#[test]
fn opaque_field_is_not_readable_from_a_foreign_global_initializer() {
    let scratch = support::Scratch::new("opaque-global-projection");
    std::fs::write(
        scratch.path().join("module.lim"),
        "(#struct Private ((value #u64)))
         (#opaque Private)
         (#const VALUE Private (#struct-literal Private ((value 42u64))))",
    )
    .unwrap();
    let source = "(#import \"module.lim\")
      (#const LEAK #u64 (#get VALUE value))
      (#fn main () #u64 (#return LEAK))";
    let result = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    );
    let error = match result {
        Ok(_) => panic!("foreign global initializer read an opaque field"),
        Err(error) => error,
    };
    assert!(error.message.contains("opaque type 'Private'"), "{error:?}");
}
