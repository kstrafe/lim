use lim::{check_types, parse_program};
use std::{fs, process::Command, time::Duration};

mod support;

fn resolve_pin_slot_import(source: &str) -> String {
    source.replace(
        "../library/pin_slot.lim",
        &format!("{}/library/pin_slot.lim", env!("CARGO_MANIFEST_DIR")),
    )
}

#[test]
fn generated_pin_slot_takes_a_linear_value_and_leaves_empty_in_place() {
    let source = "(#import \"../library/pin_slot.lim\")
      (@pin-slot (StableU64 StableU64-empty StableU64-full stable-u64-empty stable-u64-take) u64)
      (#struct Frame ((value u64) (view (#pin-ref u64)) (payload StableU64)))
      (#linear Frame)
      (#fn main () u64
        (#let-mut outside u64 3u64)
        (#let external (#pin-ref u64) (#pin-borrow outside))
        (#let-mut frame Frame
          (#struct-literal Frame
            ((value 41u64) (view external) (payload (StableU64-full 1u64)))))
        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))
        (#let view (#pin-ref u64) (#pin-borrow (#get pinned value)))
        (#pin-set-field pinned view view)
        (#let slot StableU64
          (#unsafe
            (#call stable-u64-take
              (: slot (#pin-borrow-mut (#get pinned payload))))))
        (#let extracted u64
          (#match slot
            (#case (StableU64-full value) value)
            (#case StableU64-empty (#unreachable))))
        (#let empty-slot StableU64
          (#unsafe
            (#call stable-u64-take
              (: slot (#pin-borrow-mut (#get pinned payload))))))
        (#assert (#match empty-slot
          (#case StableU64-empty true)
          (#case (StableU64-full unexpected)
            (#block (#forget unexpected) false))))
        (#let observed u64 (#deref view))
        (#pin-set-field pinned view external)
        (#drop view)
        (#drop pinned)
        (#forget frame)
        (#drop external)
        (#forget outside)
        (#return (#u64.+.wrap observed extracted)))";
    let scratch = support::Scratch::new("pinned-linear-slot");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, resolve_pin_slot_import(source)).unwrap();
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
    let generated = fs::read_dir(scratch.path().join(".lim/cache"))
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
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn generated_pin_slot_take_rejects_a_live_borrow_of_the_slot() {
    let source = "(#import \"../library/pin_slot.lim\")
      (@pin-slot (StableU64 StableU64-empty StableU64-full stable-u64-empty stable-u64-take) u64)
      (#struct Frame ((payload StableU64)))
      (#linear Frame)
      (#fn main () ()
        (#let-mut frame Frame
          (#struct-literal Frame ((payload (StableU64-full 41u64)))))
        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))
        (#let view (#pin-ref StableU64) (#pin-borrow (#get pinned payload)))
        (#unsafe
          (#call stable-u64-take
            (: slot (#pin-borrow-mut (#get pinned payload)))))
        (#drop view)
        (#drop pinned)
        (#forget frame)
        (#return ()))";
    let program = parse_program(&resolve_pin_slot_import(source)).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn a_pinned_slot_payload_can_be_borrowed_and_referenced_in_its_frame() {
    let source = "(#import \"../library/pin_slot.lim\")
      (@pin-slot (StableU64 StableU64-empty StableU64-full stable-u64-empty stable-u64-take) u64)
      (#struct Frame ((payload StableU64) (view (#pin-ref u64))))
      (#linear Frame)
      (#fn main () u64
        (#let-mut outside u64 3u64)
        (#let external (#pin-ref u64) (#pin-borrow outside))
        (#let-mut frame Frame
          (#struct-literal Frame ((payload (StableU64-full 41u64)) (view external))))
        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))
        (#let slot (#pin-ref-mut StableU64) (#pin-borrow-mut (#get pinned payload)))
        (#let payload-view (#pin-ref u64)
          (#pin-get-payload slot StableU64-full 0))
        (#pin-set-field pinned view payload-view)
        (#let observed u64 (#deref payload-view))
        (#pin-set-field pinned view external)
        (#drop payload-view)
        (#drop slot)
        (#drop pinned)
        (#forget frame)
        (#drop external)
        (#forget outside)
        (#return observed))";
    let scratch = support::Scratch::new("pinned-slot-payload-borrow");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, resolve_pin_slot_import(source)).unwrap();
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
    let source = "(#import \"../library/pin_slot.lim\")
      (@pin-slot (StableU64 StableU64-empty StableU64-full stable-u64-empty stable-u64-take) u64)
      (#struct Frame ((payload StableU64)))
      (#linear Frame)
      (#fn main () ()
        (#let-mut frame Frame
          (#struct-literal Frame ((payload (StableU64-full 41u64)))))
        (#let pinned (#pin-ref-mut Frame) (#pin-borrow-mut frame))
        (#let slot (#pin-ref-mut StableU64) (#pin-borrow-mut (#get pinned payload)))
        (#let payload-view (#pin-ref u64)
          (#pin-get-payload slot StableU64-full 0))
        (#unsafe (#call stable-u64-take (: slot slot)))
        (#drop payload-view)
        (#drop slot)
        (#drop pinned)
        (#forget frame)
        (#return ()))";
    let program = parse_program(&resolve_pin_slot_import(source)).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pinned_enum_payloads_cannot_be_extracted_by_value() {
    let source = "(#enum ValueSlot ((Full u64) Empty))
      (#fn read ((slot (#pin-ref ValueSlot))) u64
        (#return (#get-payload slot Full 0)))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("get-payload requires an enum value"),
        "{error}"
    );
}

#[test]
fn pinned_enum_payload_mut_borrow_requires_mutable_pin() {
    let source = "(#enum ValueSlot ((Full u64) Empty))
      (#fn read ((slot (#pin-ref ValueSlot))) (#pin-ref-mut u64)
        (#return (#pin-get-payload-mut slot Full 0)))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("pin-get-payload-mut requires a mutable pinned enum reference"),
        "{error}"
    );
}
