use lim::aarch64::encoder;
#[path = "../src/aarch64_elf.rs"]
mod elf;
use encoder::{Condition, Encoder};

#[test]
fn known_a64_encodings_and_forward_backward_fixups() {
    let mut code = Encoder::default();
    let top = code.label();
    let end = code.label();
    code.bind(top).unwrap();
    code.constant(0, 42);
    code.mov(1, 0);
    code.memory(false, 0, 31, 16);
    code.memory(true, 1, 31, 16);
    code.branch(end, Some(Condition::Eq), false);
    code.branch(top, None, false);
    code.bind(end).unwrap();
    code.ret();
    code.finish().unwrap();
    assert_eq!(
        code.words,
        [0xd2800540, 0xaa0003e1, 0xf9000be0, 0xf9400be1, 0x54000040, 0x17fffffb, 0xd65f03c0]
    );
}

#[test]
fn unresolved_labels_fail_closed_and_duplicate_bindings_are_errors() {
    let mut code = Encoder::default();
    let target = code.label();
    code.branch(target, None, true);
    assert!(code.finish().is_err());
    code.bind(target).unwrap();
    assert!(code.bind(target).is_err());
}

#[test]
fn elf_is_aarch64_static_rx_with_nonexecutable_stack() {
    let bytes = elf::executable(&[0xd2800540, 0xd2800bc8, 0xd4000001], 0).unwrap();
    assert_eq!(&bytes[..8], b"\x7fELF\x02\x01\x01\x00");
    assert_eq!(u16::from_le_bytes(bytes[18..20].try_into().unwrap()), 183);
    assert_eq!(
        u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        0x401000
    );
    assert_eq!(u32::from_le_bytes(bytes[68..72].try_into().unwrap()), 5);
    assert_eq!(
        u32::from_le_bytes(bytes[120..124].try_into().unwrap()),
        0x6474e551
    );
    assert_eq!(u32::from_le_bytes(bytes[124..128].try_into().unwrap()), 6);
    assert!(elf::executable(&[], 0).is_err());
    assert!(elf::executable(&[0], 1).is_err());
}
