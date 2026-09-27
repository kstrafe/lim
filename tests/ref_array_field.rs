mod support;

use std::process::Command;

#[test]
fn multiword_field_read_through_reference_keeps_its_base_address() {
    let source = "(#struct Packet ((items (#array u64 3)) (sentinel u64)))
      (#fn main () u64
        (#let packet Packet (#struct-literal Packet
          ((items (#array-of (#array u64 3) 4u64 8u64 42u64))
           (sentinel 99u64))))
        (#let packet-ref (#ref Packet) (#borrow packet))
        (#let items (#array u64 3) (#get packet-ref items))
        (#drop packet-ref)
        (#return (#index items 2u64)))";
    let scratch = support::Scratch::new("ref-array-field");
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert!(assembly.contains("mov r11, rax"));
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
