mod support;

use std::process::Command;

#[test]
fn wake_token_table_reports_invalid_busy_and_exhausted_slots() {
    let source = format!(
        "(#import \"{}/library/wake_tokens.lim\")
         (#fn main () u64
           (#let-mut table WakeTable4 (#call wake-table4-create (:)))
           (#let invalid WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut table) : slot 4usize)))
           (#let invalid-ok bool (#match invalid
             (#case WakeInvalid4 true) (#case _ false)))
           (#let first WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut table) : slot 1usize)))
           (#let token WakeToken4 (#match first
             (#case (WakeRegistered4 value) value)
             (#case _ (#unreachable))))
           (#let busy WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut table) : slot 1usize)))
           (#let busy-ok bool (#match busy
             (#case WakeBusy4 true) (#case _ false)))
           (#let retired WakeRetire4
             (#call wake-table4-retire (: table (#borrow-mut table) : token token)))
           (#let retired-ok bool (#match retired
             (#case WakeRetired4 true) (#case WakeStale4 false)))
           (#let-mut exhausted-table WakeTable4 (#struct-literal WakeTable4
             ((generations (#array-of (#array u64 4)
               1u64 18446744073709551615u64 1u64 1u64))
              (active (#array-repeat false)))))
           (#let exhausted WakeRegister4
             (#call wake-table4-register (: table (#borrow-mut exhausted-table) : slot 1usize)))
           (#let exhausted-ok bool (#match exhausted
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
