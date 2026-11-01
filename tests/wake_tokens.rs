mod support;

use std::process::Command;

#[test]
fn wake_token_table_reports_invalid_busy_and_exhausted_slots() {
    let source = format!(
        "(#alias WakeRegister4 = \"{0}/library/wake_tokens.lim::WakeRegister4\")\n(#alias WakeRetire4 = \"{0}/library/wake_tokens.lim::WakeRetire4\")\n(#alias WakeTable4 = \"{0}/library/wake_tokens.lim::WakeTable4\")\n(#alias WakeToken4 = \"{0}/library/wake_tokens.lim::WakeToken4\")\n(#alias wake-table4-create = \"{0}/library/wake_tokens.lim::wake-table4-create\")\n(#alias wake-table4-create-exhausted = \"{0}/library/wake_tokens.lim::wake-table4-create-exhausted\")\n(#alias wake-table4-register = \"{0}/library/wake_tokens.lim::wake-table4-register\")\n(#alias wake-table4-retire = \"{0}/library/wake_tokens.lim::wake-table4-retire\")\n         (#fn main () #u64\n           (#let-mut table WakeTable4 (#call wake-table4-create (:)))\n           (#let invalid WakeRegister4\n             (#call wake-table4-register (: table (#borrow-mut table) : slot 4usize)))\n           (#let invalid-ok #bool (#match invalid\n             (#case WakeRegister4.WakeInvalid4 true) (#case _ false)))\n           (#let first WakeRegister4\n             (#call wake-table4-register (: table (#borrow-mut table) : slot 1usize)))\n           (#let token WakeToken4 (#match first\n             (#case (WakeRegister4.WakeRegistered4 value) value)\n             (#case _ (#unreachable))))\n           (#let busy WakeRegister4\n             (#call wake-table4-register (: table (#borrow-mut table) : slot 1usize)))\n           (#let busy-ok #bool (#match busy\n             (#case WakeRegister4.WakeBusy4 true) (#case _ false)))\n           (#let retired WakeRetire4\n             (#call wake-table4-retire (: table (#borrow-mut table) : token token)))\n           (#let retired-ok #bool (#match retired\n             (#case WakeRetire4.WakeRetired4 true) (#case WakeRetire4.WakeStale4 false)))\n           (#let-mut exhausted-table WakeTable4\n             (#call wake-table4-create-exhausted (:)))\n           (#let exhausted WakeRegister4\n             (#call wake-table4-register (: table (#borrow-mut exhausted-table) : slot 1usize)))\n           (#let exhausted-ok #bool (#match exhausted\n             (#case WakeRegister4.WakeExhausted4 true) (#case _ false)))\n           (#forget table) (#forget exhausted-table)\n           (#return (#if\n             (#bool::and invalid-ok\n               (#bool::and busy-ok (#bool::and retired-ok exhausted-ok)))\n             42u64 0u64)))",
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
            "(#const tOKEN WakeToken4 (#struct-literal WakeToken4
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
            "(#alias WakeRegister4 = \"{0}/library/wake_tokens.lim::WakeRegister4\")\n(#alias WakeRetire4 = \"{0}/library/wake_tokens.lim::WakeRetire4\")\n(#alias WakeTable4 = \"{0}/library/wake_tokens.lim::WakeTable4\")\n(#alias WakeToken4 = \"{0}/library/wake_tokens.lim::WakeToken4\")\n(#alias wake-table4-create = \"{0}/library/wake_tokens.lim::wake-table4-create\")\n(#alias wake-table4-create-exhausted = \"{0}/library/wake_tokens.lim::wake-table4-create-exhausted\")\n(#alias wake-table4-register = \"{0}/library/wake_tokens.lim::wake-table4-register\")\n(#alias wake-table4-retire = \"{0}/library/wake_tokens.lim::wake-table4-retire\")\n(#alias wake-table4-valid = \"{0}/library/wake_tokens.lim::wake-table4-valid\")\n(#alias wake-token4-generation = \"{0}/library/wake_tokens.lim::wake-token4-generation\")\n(#alias wake-token4-slot = \"{0}/library/wake_tokens.lim::wake-token4-slot\")\n{body}",
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
        let readable = error.message.replace(
            &format!("{}/library/wake_tokens.lim::", env!("CARGO_MANIFEST_DIR")),
            "",
        );
        assert!(readable.contains(expected), "{name}: {error:?}");
        assert_eq!(error.span.expect("private access source span").source_id, 0);
    }
}

#[test]
fn external_import_prefix_does_not_remove_opacity() {
    let scratch = support::Scratch::new("wake-authority-external");
    let source = format!(
        "(#alias ExtWakeToken = \"{}/library/wake_tokens.lim::WakeToken4\")
         (#fn main () #u64
           (#let token ExtWakeToken (#struct-literal ExtWakeToken
             ((slot 0usize) (generation 1u64))))
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
            .contains("WakeToken4' outside its defining module"),
        "{error:?}"
    );
}

#[test]
fn opaque_field_is_not_readable_from_a_foreign_global_initializer() {
    let scratch = support::Scratch::new("opaque-global-projection");
    std::fs::write(
        scratch.path().join("module.lim"),
        "(#struct Private () ((value #u64)))
         (#opaque Private)
         (#const vALUE Private (#struct-literal Private ((value 42u64))))",
    )
    .unwrap();
    let source = "(#alias vALUE = ./module.lim::vALUE)
      (#const lEAK #u64 (#get vALUE value))
      (#fn main () #u64 (#return lEAK))";
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
    assert!(
        error
            .message
            .contains("Private' outside its defining module"),
        "{error:?}"
    );
}
