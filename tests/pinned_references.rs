use lim::{check_types, parse_program};
use std::{fs, process::Command, time::Duration};

mod support;

fn check(source: &str) -> Result<(), String> {
    let program = parse_program(source).map_err(|error| error.to_string())?;
    check_types(&program).map_err(|error| error.to_string())
}

#[test]
fn a_pinned_shared_reference_can_read_its_referent() {
    let source = "(#fn main () u64
      (#let owner u64 7u64)
      (#let pinned (#pin-ref u64) (#pin-borrow owner))
      (#return (#deref pinned)))";
    check(source).unwrap();
}

#[test]
fn unsafe_pin_read_and_write_preserve_a_stable_aggregate_location() {
    let source = "(#struct Pair ((left u64) (right u64)))
      (#fn main () u64
        (#let-mut owner Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
        (#let pinned (#pin-ref-mut Pair) (#pin-borrow-mut owner))
        (#let previous Pair (#unsafe (#pin-read pinned)))
        (#let previous-sum u64
          (#u64.+.wrap (#get previous left) (#get previous right)))
        (#unsafe
          (#pin-write pinned
            (#struct-literal Pair ((left 10u64) (right 20u64)))))
        (#let current Pair (#unsafe (#pin-read pinned)))
        (#let current-sum u64
          (#u64.+.wrap (#get current left) (#get current right)))
        (#drop pinned)
        (#forget owner)
        (#return (#u64.+.wrap previous-sum current-sum)))";
    let scratch = support::Scratch::new("pinned-storage-access");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(33), "{stderr:?}");
}

#[test]
fn pin_storage_reads_and_writes_require_unsafe() {
    for expression in ["(#pin-read pinned)", "(#pin-write pinned 2u64)"] {
        let source = format!(
            "(#fn main () u64
              (#let-mut owner u64 1u64)
              (#let pinned (#pin-ref-mut u64) (#pin-borrow-mut owner))
              {expression}
              (#drop pinned)
              (#return owner))"
        );
        let error = check(&source).unwrap_err();
        assert!(error.contains("unsafe operation"), "{error}");
    }
}

#[test]
fn pin_write_cannot_invalidate_a_live_projected_reference() {
    let source = "(#struct Pair ((left u64) (right u64)))
      (#fn main () ()
        (#let-mut owner Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
        (#let pinned (#pin-ref-mut Pair) (#pin-borrow-mut owner))
        (#let view (#pin-ref u64) (#borrow (#get pinned left)))
        (#unsafe
          (#pin-write pinned
            (#struct-literal Pair ((left 10u64) (right 20u64)))))
        (#drop view)
        (#drop pinned)
        (#forget owner)
        (#return ()))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pin_set_field_initializes_and_releases_a_self_reference_in_place() {
    let source = "(#struct Link ((value u64) (view (#pin-ref u64))))
      (#fn main () u64
        (#let-mut outside u64 3u64)
        (#let external (#pin-ref u64) (#pin-borrow outside))
        (#let-mut link Link
          (#struct-literal Link ((value 42u64) (view external))))
        (#let pinned (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#let view (#pin-ref u64) (#pin-borrow (#get pinned value)))
        (#pin-set-field pinned view view)
        (#let observed u64 (#deref view))
        (#pin-set-field pinned view external)
        (#drop view)
        (#drop pinned)
        (#forget link)
        (#drop external)
        (#forget outside)
        (#return observed))";
    let scratch = support::Scratch::new("pin-self-reference-field");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn pin_set_field_updates_disjoint_copy_state_while_a_field_is_borrowed() {
    let source = "(#struct Pair ((value u64) (state u32)))
      (#fn main () u64
        (#let-mut pair Pair
          (#struct-literal Pair ((value 40u64) (state 0u32))))
        (#let pinned (#pin-ref-mut Pair) (#pin-borrow-mut pair))
        (#let view (#pin-ref u64) (#pin-borrow (#get pinned value)))
        (#pin-set-field pinned state 2u32)
        (#let observed u64 (#deref view))
        (#drop view)
        (#let state u32 (#get pinned state))
        (#drop pinned)
        (#forget pair)
        (#return (#u64.+.wrap observed (#as state u64))))";
    let scratch = support::Scratch::new("pin-state-field-write");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn pin_set_field_cannot_write_the_referent_of_a_live_pin() {
    let source = "(#struct Pair ((value u64) (state u32)))
      (#fn main () ()
        (#let-mut pair Pair
          (#struct-literal Pair ((value 40u64) (state 0u32))))
        (#let pinned (#pin-ref-mut Pair) (#pin-borrow-mut pair))
        (#let view (#pin-ref u64) (#pin-borrow (#get pinned value)))
        (#pin-set-field pinned value 41u64)
        (#drop view)
        (#drop pinned)
        (#forget pair)
        (#return ()))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pin_set_field_updates_a_fieldless_enum_state_in_place() {
    let source = "(#enum State (Idle Running))
      (#struct Pair ((value u64) (state State)))
      (#fn main () u64
        (#let-mut pair Pair
          (#struct-literal Pair ((value 40u64) (state Idle))))
        (#let pinned (#pin-ref-mut Pair) (#pin-borrow-mut pair))
        (#let view (#pin-ref u64) (#pin-borrow (#get pinned value)))
        (#pin-set-field pinned state Running)
        (#let observed u64 (#deref view))
        (#drop view)
        (#let state State (#get pinned state))
        (#drop pinned)
        (#forget pair)
        (#return (#u64.+.wrap observed (#as state u64))))";
    let scratch = support::Scratch::new("pin-enum-state-field-write");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
fn pin_set_field_rejects_replacing_a_borrowed_reference_field() {
    let source = "(#struct Link ((value u64) (view (#pin-ref u64))))
      (#fn main () ()
        (#let-mut outside u64 3u64)
        (#let external (#pin-ref u64) (#pin-borrow outside))
        (#let-mut link Link
          (#struct-literal Link ((value 42u64) (view external))))
        (#let pinned (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#let view (#pin-ref (#pin-ref u64)) (#borrow (#get pinned view)))
        (#pin-set-field pinned view external)
        (#drop view)
        (#drop pinned)
        (#forget link)
        (#drop external)
        (#forget outside)
        (#return ()))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pin_set_field_does_not_duplicate_mutable_references() {
    let source = "(#struct Link ((view (#pin-ref-mut u64))))
      (#fn main () ()
        (#let-mut target u64 3u64)
        (#let replacement (#pin-ref-mut u64) (#pin-borrow-mut target))
        (#let-mut link Link (#struct-literal Link ((view replacement))))
        (#let pinned (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#pin-set-field pinned view replacement)
        (#drop pinned)
        (#forget link)
        (#drop replacement)
        (#forget target)
        (#return ()))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("Copy scalar or shared-reference field"),
        "{error}"
    );
}

#[test]
fn a_stored_self_reference_keeps_its_pinned_owner_borrowed() {
    let source = "(#struct Link ((value u64) (view (#pin-ref u64))))
      (#fn main () ()
        (#let-mut outside u64 3u64)
        (#let external (#pin-ref u64) (#pin-borrow outside))
        (#let-mut link Link
          (#struct-literal Link ((value 42u64) (view external))))
        (#let pinned (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#let view (#pin-ref u64) (#pin-borrow (#get pinned value)))
        (#pin-set-field pinned view view)
        (#drop view)
        (#drop pinned)
        (#forget link)
        (#drop external)
        (#forget outside)
        (#return ()))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn a_pinned_referent_cannot_be_copied_while_the_pin_is_live() {
    let source = "(#fn main () u64
      (#let owner u64 7u64)
      (#let pinned (#pin-ref u64) (#pin-borrow owner))
      (#let snapshot u64 owner)
      (#return (#u64.+.wrap snapshot (#deref pinned))))";
    let error = check(source).unwrap_err();
    assert!(error.contains("pinned referent"), "{error}");
}

#[test]
fn a_pinned_linear_referent_cannot_be_moved() {
    let source = "(#struct Resource ((value u64)))
      (#linear Resource)
      (#fn main () u64
        (#let owner Resource (#struct-literal Resource ((value 7u64))))
        (#let pinned (#pin-ref Resource) (#pin-borrow owner))
        (#let moved Resource owner)
        (#forget moved)
        (#return (#get (#deref pinned) value)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("pinned"),
        "{error}"
    );
}

#[test]
fn a_pinned_mutable_reference_cannot_replace_its_referent() {
    let source = "(#fn main () ()
      (#let-mut owner u64 7u64)
      (#let pinned (#pin-ref-mut u64) (#pin-borrow-mut owner))
      (#deref-set pinned 8u64)
      (#return ()))";
    let error = check(source).unwrap_err();
    assert!(error.contains("would replace the referent"), "{error}");
}

#[test]
fn fields_of_a_pinned_referent_cannot_be_replaced_implicitly() {
    let source = "(#struct Pair ((left u64)))
      (#fn main () u64
        (#let-mut pair Pair (#struct-literal Pair ((left 7u64))))
        (#let pinned (#pin-ref-mut Pair) (#pin-borrow-mut pair))
        (#set-field pinned left 8u64)
        (#return (#get (#deref pinned) left)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("pinned") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn a_live_pin_prevents_mutating_the_original_owner() {
    let source = "(#fn main () u64
      (#let-mut owner u64 7u64)
      (#let pinned (#pin-ref u64) (#pin-borrow owner))
      (#set owner 8u64)
      (#return (#deref pinned)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("mutate"),
        "{error}"
    );
}

#[test]
fn dropping_the_pin_releases_the_referent() {
    let source = "(#fn main () u64
      (#let-mut owner u64 7u64)
      (#let pinned (#pin-ref u64) (#pin-borrow owner))
      (#drop pinned)
      (#set owner 8u64)
      (#return owner))";
    check(source).unwrap();
}

#[test]
fn a_stack_pin_cannot_escape_its_owner_function() {
    let source = "(#fn make-pin () (#pin-ref u64)
      (#let owner u64 7u64)
      (#return (#pin-borrow owner)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("outlive") || error.contains("return"),
        "{error}"
    );
}

#[test]
fn a_stack_pin_cannot_escape_inside_an_aggregate() {
    let source = "(#struct Holder ((value (#pin-ref u64))))
      (#fn make-holder () Holder
        (#let owner u64 7u64)
        (#let pinned (#pin-ref u64) (#pin-borrow owner))
        (#return (#struct-literal Holder ((value pinned)))))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("outlive") || error.contains("return"),
        "{error}"
    );
}

#[test]
fn a_pinned_owner_cannot_be_destroyed_until_its_pin_is_dropped() {
    let source = "(#struct Resource ((value u64)))
      (#linear Resource)
      (#fn main () u64
        (#let owner Resource (#struct-literal Resource ((value 7u64))))
        (#let pinned (#pin-ref Resource) (#pin-borrow owner))
        (#drop owner)
        (#drop pinned)
        (#return 0u64))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("pinned"),
        "{error}"
    );
}

#[test]
fn dropping_a_pin_allows_its_linear_owner_to_be_destroyed() {
    let source = "(#struct Resource ((value u64)))
      (#linear Resource)
      (#fn main () u64
        (#let owner Resource (#struct-literal Resource ((value 7u64))))
        (#let pinned (#pin-ref Resource) (#pin-borrow owner))
        (#drop pinned)
        (#drop owner)
        (#return 0u64))";
    check(source).unwrap();
}

#[test]
fn an_unsafe_pinned_pointer_borrow_keeps_the_anchor_loan() {
    let source = "(#fn main () u64
      (#let owner u64 42u64)
      (#let pointer (#ptr u64) (#unsafe (#addr-of owner)))
      (#let anchor (#pin-ref u64) (#pin-borrow owner))
      (#let pinned (#pin-ref u64)
        (#unsafe (#pin-ptr-borrow anchor pointer)))
      (#return (#deref pinned)))";
    let scratch = support::Scratch::new("pinned-pointer-borrow");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn a_pinned_pointer_borrow_rejects_mutating_its_anchor() {
    let source = "(#fn main () u64
      (#let-mut owner u64 7u64)
      (#let pointer (#ptr-mut u64) (#unsafe (#addr-of-mut owner)))
      (#let anchor (#pin-ref-mut u64) (#pin-borrow-mut owner))
      (#let pinned (#pin-ref-mut u64)
        (#unsafe (#pin-ptr-borrow-mut anchor pointer)))
      (#set owner 9u64)
      (#return (#deref pinned)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("pinned"),
        "{error}"
    );
}

#[test]
fn pinned_pointer_borrows_require_pinned_anchors() {
    let source = "(#fn main () u64
      (#let value u64 7u64)
      (#let pointer (#ptr u64) (#unsafe (#addr-of value)))
      (#let pinned (#pin-ref u64)
        (#unsafe (#pin-ptr-borrow (#borrow value) pointer)))
      (#return (#deref pinned)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("pinned-reference lifetime anchor"),
        "{error}"
    );
}

#[test]
fn pinned_pointer_borrows_require_unsafe_context() {
    let source = "(#fn main () u64
      (#let value u64 7u64)
      (#let anchor (#pin-ref u64) (#pin-borrow value))
      (#let pointer (#ptr u64) (#unsafe (#addr-of value)))
      (#let pinned (#pin-ref u64) (#pin-ptr-borrow anchor pointer))
      (#return (#deref pinned)))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("unsafe operation 'pin-ptr-borrow'"),
        "{error}"
    );
}

#[test]
fn a_pinned_pointer_borrow_cannot_escape_its_stack_anchor() {
    let source = "(#fn make-pin () (#pin-ref u64)
      (#let owner u64 7u64)
      (#let pointer (#ptr u64) (#unsafe (#addr-of owner)))
      (#let anchor (#pin-ref u64) (#pin-borrow owner))
      (#return (#unsafe (#pin-ptr-borrow anchor pointer))))";
    let error = check(source).unwrap_err();
    assert!(
        error.contains("outlive") || error.contains("return"),
        "{error}"
    );
}

#[test]
fn a_pin_stays_effective_when_stored_in_an_aggregate() {
    let source = "(#fn main () u64
      (#let owner u64 7u64)
      (#let pinned (#pin-ref u64) (#pin-borrow owner))
      (#let holder (#tuple (#pin-ref u64))
        (#tuple (#tuple (#pin-ref u64)) pinned))
      (#let snapshot u64 owner)
      (#return (#u64.+.wrap snapshot (#deref (#get holder 0)))))";
    let error = check(source).unwrap_err();
    assert!(error.contains("pinned referent"), "{error}");
}

#[test]
fn a_pin_stays_effective_across_a_reference_returning_function() {
    let source = "(#fn retain ((value (#pin-ref u64))) (#pin-ref u64)
        (#return value))
      (#fn main () u64
        (#let owner u64 7u64)
        (#let pinned (#pin-ref u64) (#pin-borrow owner))
        (#let retained (#pin-ref u64) (#call retain (: value pinned)))
        (#let snapshot u64 owner)
        (#return (#u64.+.wrap snapshot (#deref retained))))";
    let error = check(source).unwrap_err();
    assert!(error.contains("pinned referent"), "{error}");
}

#[test]
fn field_reborrows_preserve_the_pin() {
    let source = "(#struct Pair ((left u64) (right u64)))
      (#fn main () u64
        (#let pair Pair (#struct-literal Pair ((left 7u64) (right 8u64))))
        (#let pinned (#pin-ref Pair) (#pin-borrow pair))
        (#let left-pin (#pin-ref u64) (#borrow (#get pinned left)))
        (#let copied u64 (#get pair left))
        (#return (#u64.+.wrap copied (#deref left-pin))))";
    let error = check(source).unwrap_err();
    assert!(error.contains("pinned referent"), "{error}");
}

#[test]
fn a_pinned_reference_runs_through_the_native_backend() {
    let source = "(#fn main () u64
      (#let owner u64 42u64)
      (#let pinned (#pin-ref u64) (#pin-borrow owner))
      (#return (#deref pinned)))";
    let scratch = support::Scratch::new("pinned-reference");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn a_pinned_field_reborrow_runs_through_the_native_backend() {
    let source = "(#struct Pair ((left u64) (right u64)))
      (#fn main () u64
        (#let pair Pair (#struct-literal Pair ((left 40u64) (right 2u64))))
        (#let pinned (#pin-ref Pair) (#pin-borrow pair))
        (#let left-pin (#pin-ref u64) (#borrow (#get pinned left)))
        (#return (#deref left-pin)))";
    let scratch = support::Scratch::new("pinned-field-reborrow");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(40), "{stderr:?}");
}

#[test]
fn a_pinned_reference_can_cross_a_function_boundary_natively() {
    let source = "(#fn retain ((value (#pin-ref u64))) (#pin-ref u64)
        (#return value))
      (#fn main () u64
        (#let owner u64 42u64)
        (#let pinned (#pin-ref u64) (#pin-borrow owner))
        (#let retained (#pin-ref u64) (#call retain (: value pinned)))
        (#return (#deref retained)))";
    let scratch = support::Scratch::new("pinned-function-return");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}
