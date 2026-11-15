mod support;

use std::{fs, process::Command, time::Duration};

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("pin-ownership");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(
        status.code(),
        Some(expected),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn generated_stack_scope_runs_with_in_place_cleanup() {
    run(
        &include_str!("../examples/stationary_pin.lim").replace(
            "../library/pin.lim",
            &format!("{}/library/pin.lim", env!("CARGO_MANIFEST_DIR")),
        ),
        42,
    );
}

#[test]
fn movable_heap_owners_initialize_native_scalars_and_large_aggregates() {
    for (ty, value, read) in [
        ("#u32", "42u32", "(#as (#deref view) #u64)"),
        (
            "(#array #u64 8)",
            "(#array-of (#array #u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 42u64)",
            "(#index view 7usize)",
        ),
    ] {
        let source = format!(
            "#fn forward {{
  #params = ((owner (#pin-own {ty})));
  #returns = (#pin-own {ty});
  #body = ( (#return owner)
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
            (#let pointer (#ptr-mut {ty}) (#unsafe (#linux-syscall (#ptr-mut {ty}) 9usize
              (0usize (#size-of {ty}) 3usize 34usize -1i64 0usize))))
            (#let owner (#pin-own {ty}) (#unsafe (#pin-own-of pointer {value})))
            (#let view (#pin-ref {ty}) (#pin-own-borrow owner))
            (#let moved (#pin-own {ty}) (#call forward ((owner owner))))
            (#let result #u64 {read}) (#forget view)
            (#let raw (#ptr-mut {ty}) (#unsafe (#pin-release moved)))
            (#let status #i64 (#unsafe (#linux-syscall #i64 11usize (raw (#size-of {ty})))))
            (#assert (#i64::eq status 0i64)) (#return result)\n  );\n}}\n"
        );
        run(&source, 42);
    }
}

#[test]
fn pin_owned_reference_enum_initialization_preserves_inactive_and_live_slots() {
    for initializer in ["Slot.Empty", "(Slot.Full (#borrow source))"] {
        let source = format!(
            "#enum Slot () ((Slot.Empty) (Slot.Full (#ref #u64)))
#struct Holder () ((slot Slot))
#fn forward {{
  #params = ((owner (#pin-own Holder)));
  #returns = (#pin-own Holder);
  #body = ( (#return owner)
  );
}}
#fn read {{
  #params = ((view (#pin-ref Holder)));
  #returns = #u64;
  #body = (
              (#return (#if (#variant-is (#pin-borrow (#get view slot)) Slot.Empty) 42u64
                (#deref (#deref (#unsafe (#pin-get-payload-unchecked (#pin-borrow (#get view slot)) Slot.Full))))))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
              (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
                (0usize (#size-of Holder) 3usize 34usize -1i64 0usize))))
              (#let-mut source #u64 42u64)
              (#let initial Holder (#struct-literal Holder ((slot {initializer}))))
              (#let-mut owner (#pin-own Holder) (#unsafe (#pin-own-of pointer initial)))
              (#let view (#pin-ref Holder) (#pin-own-borrow owner))
              (#let result #u64 (#call read ((view view)))) (#forget view)
              (#let moved (#pin-own Holder) (#call forward ((owner owner))))
              (#let raw (#ptr-mut Holder) (#unsafe (#pin-release moved)))
              (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (raw (#size-of Holder)))) 0i64))
              (#return result)\n  );\n}}\n"
        );
        run(&source, 42);
        if initializer == "Slot.Empty" {
            let changed = source.replace("(#let view", "(#let update (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))\n            (#unsafe (#forget (#pin-read (#pin-borrow-mut (#get update slot)))))\n            (#unsafe (#pin-write (#pin-borrow-mut (#get update slot)) (Slot.Full (#borrow source))))\n            (#forget update)\n            (#let view");
            run(&changed, 42);
            let invalid = changed.replace("(#let raw", "(#set source 99u64) (#let raw");
            let scratch = support::Scratch::new("pin-owned-updated-enum-conflict");
            let error = lim::compile_source_to_assembly(
                &invalid,
                &scratch.path().join("main.lim"),
                &lim::CompileConfig::default(),
                &scratch.path().join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .expect_err("an initial Slot.Empty fact must not hide a newly stored live reference");
            assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        }
        if initializer.starts_with("(Slot.Full") {
            let rejected = source.replace("(#let raw", "(#set source 99u64) (#let raw");
            let scratch = support::Scratch::new("pin-owned-reference-enum-conflict");
            let error = lim::compile_source_to_assembly(
                &rejected,
                &scratch.path().join("main.lim"),
                &lim::CompileConfig::default(),
                &scratch.path().join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .expect_err("the live stored reference must keep its source borrowed");
            assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        }
    }
}
