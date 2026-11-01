use lim::{check_types, parse_program};
use std::{fs, process::Command, time::Duration};

mod support;

fn pin_slot_source(source: &str) -> String {
    format!(
        "(#alias lim-gen-pin-slot = \"{}/library/pin_slot.lim::#pin-slot\")\n{source}",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[test]
fn generated_pin_slot_takes_a_linear_value_and_leaves_empty_in_place() {
    let source = "\n      (#generate lim-gen-pin-slot (StableU64 StableU64.Empty StableU64.Full stable-u64-empty stable-u64-take StableU64Insert StableU64Insert.Inserted StableU64Insert.Occupied stable-u64-try-insert) #u64)\n      (#struct Frame (#linear) ((value #u64) (view (#pin-ref #u64)) (payload StableU64)))\n\n      (#fn main () #u64\n        (#let-mut outside #u64 3u64)\n        (#let external (#pin-ref #u64) (#pin-borrow outside))\n        (#let-mut frame Frame\n          (#struct-literal Frame\n            ((value 41u64) (view external) (payload (StableU64.Full 1u64)))))\n        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))\n        (#let view (#pin-ref #u64) (#pin-borrow (#get pinned value)))\n        (#pin-set-field pinned view view)\n        (#let slot StableU64\n          (#unsafe\n            (#unsafe-call stable-u64-take\n              (: slot (#pin-borrow-mut (#get pinned payload))))))\n        (#let extracted #u64\n          (#match slot\n            (#case (StableU64.Full value) value)\n            (#case StableU64.Empty (#unreachable))))\n        (#let empty-slot StableU64\n          (#unsafe\n            (#unsafe-call stable-u64-take\n              (: slot (#pin-borrow-mut (#get pinned payload))))))\n        (#assert (#match empty-slot\n          (#case StableU64.Empty true)\n          (#case (StableU64.Full unexpected)\n            (#block (#forget unexpected) false))))\n        (#let observed #u64 (#deref view))\n        (#pin-set-field pinned view external)\n        (#drop view)\n        (#drop pinned)\n        (#forget frame)\n        (#drop external)\n        (#forget outside)\n        (#return (#u64::add-wrap observed extracted)))";
    let scratch = support::Scratch::new("pinned-linear-slot");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, pin_slot_source(source)).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        64 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
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
    assert!(
        generated.contains("#unsafe-fn stable-u64-take"),
        "{generated}"
    );
    assert!(
        generated.contains("(#forget (#pin-read slot))"),
        "try-insert must consume the initialized empty shell before refilling: {generated}"
    );
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn generated_pin_slot_take_rejects_a_live_borrow_of_the_slot() {
    let source = "\n      (#generate lim-gen-pin-slot (StableU64 StableU64.Empty StableU64.Full stable-u64-empty stable-u64-take StableU64Insert StableU64Insert.Inserted StableU64Insert.Occupied stable-u64-try-insert) #u64)\n      (#struct Frame (#linear) ((payload StableU64)))\n\n      (#fn main () ()\n        (#let-mut frame Frame\n          (#struct-literal Frame ((payload (StableU64.Full 41u64)))))\n        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))\n        (#let view (#pin-ref StableU64) (#pin-borrow (#get pinned payload)))\n        (#unsafe\n          (#unsafe-call stable-u64-take\n            (: slot (#pin-borrow-mut (#get pinned payload)))))\n        (#drop view)\n        (#drop pinned)\n        (#forget frame)\n        (#return ()))";
    let program = parse_program(&pin_slot_source(source)).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn generated_pin_slot_try_insert_refills_in_place_and_returns_occupied_input() {
    let source = "\n      (#generate lim-gen-pin-slot (StableU64 StableU64.Empty StableU64.Full stable-u64-empty stable-u64-take StableU64Insert StableU64Insert.Inserted StableU64Insert.Occupied stable-u64-try-insert) #u64)\n      (#fn main () #u64\n        (#let-mut slot StableU64 (#call stable-u64-empty (:)))\n        (#let pinned (#pin-ref-mut StableU64) (#pin-borrow-mut slot))\n        (#let first StableU64Insert\n          (#call stable-u64-try-insert (: slot pinned : value 41u64)))\n        (#match first\n          (#case StableU64Insert.Inserted ())\n          (#case (StableU64Insert.Occupied value) (#forget value)))\n        (#let second StableU64Insert\n          (#call stable-u64-try-insert (: slot pinned : value 99u64)))\n        (#let returned #u64\n          (#match second\n            (#case StableU64Insert.Inserted (#unreachable))\n            (#case (StableU64Insert.Occupied value) value)))\n        (#let contents StableU64\n          (#unsafe (#unsafe-call stable-u64-take (: slot pinned))))\n        (#let stored #u64\n          (#match contents\n            (#case StableU64.Empty (#unreachable))\n            (#case (StableU64.Full value) value)))\n        (#drop pinned)\n        (#forget slot)\n        (#return (#u64::add-wrap returned stored)))";
    let scratch = support::Scratch::new("pinned-slot-try-insert");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, pin_slot_source(source)).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        64 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
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
    assert!(generated.contains("stable-u64-try-insert"), "{generated}");
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(140), "{stderr:?}");
}

#[test]
fn a_pinned_slot_payload_can_be_borrowed_and_referenced_in_its_frame() {
    let source = "\n      (#generate lim-gen-pin-slot (StableU64 StableU64.Empty StableU64.Full stable-u64-empty stable-u64-take StableU64Insert StableU64Insert.Inserted StableU64Insert.Occupied stable-u64-try-insert) #u64)\n      (#struct Frame (#linear) ((payload StableU64) (view (#pin-ref #u64))))\n\n      (#fn main () #u64\n        (#let-mut outside #u64 3u64)\n        (#let external (#pin-ref #u64) (#pin-borrow outside))\n        (#let-mut frame Frame\n          (#struct-literal Frame ((payload (StableU64.Full 41u64)) (view external))))\n        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))\n        (#let slot (#pin-ref-mut StableU64) (#pin-borrow-mut (#get pinned payload)))\n        (#let payload-view (#pin-ref #u64)\n          (#unsafe (#pin-get-payload-unchecked slot StableU64.Full)))\n        (#pin-set-field pinned view payload-view)\n        (#let observed #u64 (#deref payload-view))\n        (#pin-set-field pinned view external)\n        (#drop payload-view)\n        (#drop slot)\n        (#drop pinned)\n        (#forget frame)\n        (#drop external)\n        (#forget outside)\n        (#return observed))";
    let scratch = support::Scratch::new("pinned-slot-payload-borrow");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, pin_slot_source(source)).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        64 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(41), "{stderr:?}");
}

#[test]
fn a_pinned_slot_payload_loan_prevents_moving_out_the_slot() {
    let source = "\n      (#generate lim-gen-pin-slot (StableU64 StableU64.Empty StableU64.Full stable-u64-empty stable-u64-take StableU64Insert StableU64Insert.Inserted StableU64Insert.Occupied stable-u64-try-insert) #u64)\n      (#struct Frame (#linear) ((payload StableU64)))\n\n      (#fn main () ()\n        (#let-mut frame Frame\n          (#struct-literal Frame ((payload (StableU64.Full 41u64)))))\n        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))\n        (#let slot (#pin-ref-mut StableU64) (#pin-borrow-mut (#get pinned payload)))\n        (#let payload-view (#pin-ref #u64)\n          (#unsafe (#pin-get-payload-unchecked slot StableU64.Full)))\n        (#unsafe (#unsafe-call stable-u64-take (: slot slot)))\n        (#drop payload-view)\n        (#drop slot)\n        (#drop pinned)\n        (#forget frame)\n        (#return ()))";
    let program = parse_program(&pin_slot_source(source)).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pinned_enum_payloads_cannot_be_extracted_by_value() {
    let source = "(#enum ValueSlot () ((ValueSlot.Full #u64) ValueSlot.Empty))
      (#fn read ((slot (#pin-ref ValueSlot))) #u64
        (#return (#get-payload slot ValueSlot.Full 0)))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("get-payload requires an enum value"),
        "{error}"
    );
}

#[test]
fn pinned_enum_payload_mut_borrow_requires_mutable_pin() {
    let source = "(#enum ValueSlot () ((ValueSlot.Full #u64) ValueSlot.Empty))
      (#fn read ((slot (#pin-ref ValueSlot))) (#pin-ref-mut #u64)
        (#return (#unsafe (#pin-get-payload-unchecked-mut slot ValueSlot.Full))))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("pin-get-payload-unchecked-mut requires a mutable pinned enum reference"),
        "{error}"
    );
}
