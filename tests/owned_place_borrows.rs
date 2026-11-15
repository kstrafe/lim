use lim::{check_types, parse_program, DiagnosticCode};
use std::{fs, process::Command, time::Duration};

mod support;

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

fn native(source: &str, expected: i32) {
    check(source).unwrap();
    let scratch = support::Scratch::new("owned-place-borrow");
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
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected), "{stderr:?}");
}

fn diagnostic(source: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new("owned-place-borrow-diagnostic");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

fn assert_local_return_escape(source: &str, returned: &str, local: &str) {
    let error = diagnostic(source);
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    assert!(
        error
            .message
            .contains(&format!("reference to local '{local}'")),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(span.source_id, 0);
    assert_eq!(span.start, source.find(returned).unwrap(), "{error:?}");
    assert_eq!(&source[span.start..span.end], returned, "{error:?}");
    assert!(!error.labels.is_empty(), "{error:?}");
}

#[test]
fn owned_nested_fields_pin_borrow_without_copying_the_owner() {
    native(
        "#struct Inner () ((padding #u64) (value #u64))
#struct Owner (#linear) ((padding #u64) (inner Inner))
#fn main () #u64
             (#let owner Owner (#struct-literal Owner
               ((padding 9u64) (inner (#struct-literal Inner ((padding 8u64) (value 42u64)))))))
             (#let view (#pin-ref #u64) (#pin-borrow (#get (#get owner inner) value)))
             (#let result #u64 (#deref view))
             (#drop view) (#forget owner) (#return result)\n",
        42,
    );
}

#[test]
fn returned_reborrow_survives_consuming_its_parameter_handle() {
    native(
        "#struct Pair () ((left #u64) (right #u64))
#fn pick ((target (#ref-mut Pair))) (#ref-mut #u64)
             (#let child (#ref-mut #u64) (#borrow-mut (#get target left)))
             (#forget target)
             (#return child)
#fn main () #u64
             (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
             (#let child (#ref-mut #u64) (#call pick ((target (#borrow-mut pair)))))
             (#deref-set child 40u64)
             (#let result #u64 (#u64::add-wrap (#deref child) (#get pair right)))
             (#forget child) (#forget pair) (#return result)\n",
        42,
    );
}

#[test]
fn returned_aggregate_reborrow_survives_consuming_its_parameter_handle() {
    native(
        "#struct Pair () ((left #u64) (right #u64))
#struct View () ((selected (#ref-mut #u64)))
#fn pick ((target (#ref-mut Pair))) View
             (#let child (#ref-mut #u64) (#borrow-mut (#get target left)))
             (#forget target)
             (#return (#struct-literal View ((selected child))))
#fn main () #u64
             (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
             (#let view View (#call pick ((target (#borrow-mut pair)))))
             (#set-field pair right 5u64)
             (#let child (#ref-mut #u64) (#get view selected))
             (#deref-set child 40u64)
             (#let result #u64 (#u64::add-wrap (#deref child) (#get pair right)))
             (#forget child) (#forget pair) (#return result)\n",
        45,
    );
}

#[test]
fn disjoint_owned_fields_mutably_borrow_and_reborrow_in_place() {
    native(
        "#struct Pair () ((left #u64) (right #u64))
#struct Owner () ((padding #u64) (pair Pair))
#fn main () #u64
             (#let-mut owner Owner (#struct-literal Owner
               ((padding 7u64) (pair (#struct-literal Pair ((left 1u64) (right 2u64)))))))
             (#let parent (#ref-mut Pair) (#borrow-mut (#get owner pair)))
             (#let child (#ref-mut #u64) (#borrow-mut (#get parent left)))
             (#deref-set child 40u64)
             (#let right (#ref-mut #u64) (#borrow-mut (#get parent right)))
             (#deref-set right 2u64)
             (#drop right) (#drop child) (#drop parent)
             (#return (#u64::add-wrap (#get (#get owner pair) left) (#get (#get owner pair) right)))\n",
        42,
    );
}

#[test]
fn owned_tuple_array_and_mixed_projections_address_original_storage() {
    native(
        "#struct Row () ((padding #u64) (items (#array (#tuple #u64 #u64) 2)))
#fn main () #u64
             (#let-mut owner Row (#struct-literal Row
               ((padding 99u64) (items (#array (#array (#tuple #u64 #u64) 2)
                 (#tuple (#tuple #u64 #u64) 1u64 2u64)
                 (#tuple (#tuple #u64 #u64) 3u64 4u64))))))
             (#let index #usize 1usize)
             (#let view (#ref-mut #u64) (#borrow-mut (#get (#index (#get owner items) index) 1)))
             (#deref-set view 42u64)
             (#let result #u64 (#deref view))
             (#drop view) (#forget owner) (#return result)\n",
        42,
    );
}

#[test]
fn owned_array_projection_evaluates_dynamic_index_once() {
    native(
        "#fn next ((count (#ref-mut #u64))) #usize
             (#deref-set count (#u64::add-wrap (#deref count) 1u64)) (#return 1usize)
#fn main () #u64
             (#let owner (#array #u64 3) (#array (#array #u64 3) 5u64 41u64 7u64))
             (#let-mut count #u64 0u64)
             (#let view (#pin-ref #u64)
               (#pin-borrow (#index owner (#call next ((count (#borrow-mut count)))))))
             (#return (#u64::add-wrap (#deref view) count))\n",
        42,
    );
}

#[test]
fn scoped_owned_array_borrow_evaluates_index_before_its_body() {
    native(
        "#fn next ((count (#ref-mut #u64))) #usize
             (#deref-set count (#u64::add-wrap (#deref count) 1u64)) (#return 1usize)
#fn main () #u64
             (#let owner (#array #u64 2) (#array (#array #u64 2) 5u64 41u64))
             (#let-mut count #u64 0u64)
             (#return (#borrow (#index owner (#call next ((count (#borrow-mut count)))))
               (#u64::add-wrap 41u64 count)))\n",
        42,
    );
}

#[test]
fn owned_enum_payload_and_nested_field_borrows_address_the_same_slot() {
    native(
        "#struct Pair () ((left #u64) (right #u64))
#enum Choice () (Choice.Empty (Choice.Full (#tuple #u64 Pair)))
#fn main () #u64
             (#let-mut owner Choice (Choice.Full (#tuple 9u64 (#struct-literal Pair ((left 1u64) (right 2u64))))))
             (#let view (#ref-mut #u64) (#borrow-mut (#get (#get (#get-payload owner Choice.Full 0) 1) right)))
             (#deref-set view 42u64)
             (#let result #u64 (#deref view))
             (#drop view) (#forget owner) (#return result)\n",
        42,
    );
}

#[test]
fn pinned_array_reborrow_inherits_pinning_and_native_layout() {
    native(
        "#fn main () #u64
             (#let-mut owner (#array #u64 2) (#array (#array #u64 2) 3u64 4u64))
             (#let parent (#pin-ref-mut (#array #u64 2)) (#pin-borrow-mut owner))
             (#let child (#pin-ref-mut #u64) (#borrow-mut (#index parent 1usize)))
             (#unsafe (#pin-write child 42u64))
             (#drop child)
             (#let result #u64 (#index parent 1usize))
             (#drop parent) (#forget owner) (#return result)\n",
        42,
    );
}

#[test]
fn owned_field_borrow_keeps_reference_bearing_initializer_provenance() {
    native(
        "#struct Holder () ((padding #u64) (view (#ref #u64)))
#fn main () #u64
             (#let outside #u64 42u64)
             (#let owner Holder (#struct-literal Holder ((padding 1u64) (view (#borrow outside)))))
             (#let view (#pin-ref (#ref #u64)) (#pin-borrow (#get owner view)))
             (#return (#deref (#deref view)))\n",
        42,
    );
}

#[test]
fn owned_projection_borrow_cannot_escape_its_local_root() {
    for (declarations, binding, place) in [
        (
            "#struct Owner () ((value #u64))\n",
            "(#let owner Owner (#struct-literal Owner ((value 42u64))))",
            "(#get owner value)",
        ),
        (
            "",
            "(#let owner (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) 1u64 42u64))",
            "(#get owner 1)",
        ),
        (
            "",
            "(#let owner (#array #u64 2) (#array (#array #u64 2) 1u64 42u64))",
            "(#index owner 1usize)",
        ),
    ] {
        for operator in ["#borrow", "#pin-borrow"] {
            let ty = if operator == "#borrow" {
                "#ref"
            } else {
                "#pin-ref"
            };
            let borrow = format!("({operator} {place})");
            let returned = format!("(#return {borrow})");
            let source = format!("{declarations}\n#fn leak () ({ty} #u64) {binding} {returned}\n");
            let error = diagnostic(&source);
            assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
            let span = error.span.unwrap();
            assert_eq!(span.source_id, 0);
            let operand = &source[span.start..span.end];
            assert!(
                operand == place || operand == borrow || operand == returned,
                "{operand}: {error:?}"
            );
            assert!(error.message.contains("local"), "{error:?}");
        }
    }
}

#[test]
fn owned_projection_borrow_rejects_owner_move_while_loan_is_live() {
    let source = "#struct Owner (#linear) ((value #u64))
#fn main () #u64
            (#let owner Owner (#struct-literal Owner ((value 42u64))))
            (#let view (#pin-ref #u64) (#pin-borrow (#get owner value)))
            (#let moved Owner owner)
            (#let result #u64 (#deref view))
            (#drop view) (#forget moved) (#return result)\n";
    let error = diagnostic(source);
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "(#deref view)", "{error:?}");
    assert_eq!(span.start, source.find("(#deref view)").unwrap());
    let consumed = source.find("(#let moved Owner owner)").unwrap() + "(#let moved Owner ".len();
    assert!(
        error.labels.iter().any(|label| {
            label.message.contains("consumed")
                && label.span.start == consumed
                && &source[label.span.start..label.span.end] == "owner"
        }),
        "{error:?}"
    );
}

#[test]
fn borrowing_an_owned_linear_projection_does_not_consume_the_owner() {
    let source = "#struct Item (#linear) ((value #u64))
#struct Owner () ((item Item))
#fn main () #u64
            (#let owner Owner (#struct-literal Owner
              ((item (#struct-literal Item ((value 42u64)))))))
            (#let view (#pin-ref Item) (#pin-borrow (#get owner item)))
            (#drop view) (#return 0u64)\n";
    let error = diagnostic(source);
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(error.message.contains("must be consumed"), "{error:?}");
}

#[test]
fn copying_a_reference_field_preserves_external_but_not_stack_origin() {
    for (operator, ty) in [
        ("#borrow", "#ref"),
        ("#pin-borrow", "#pin-ref"),
        ("#borrow-mut", "#ref-mut"),
        ("#pin-borrow-mut", "#pin-ref-mut"),
    ] {
        let valid = format!(
            "#struct Holder () ((view (#ref #u64)))
#fn read ((outside (#ref #u64))) (#ref #u64)
                 (#let-mut owner Holder (#struct-literal Holder ((view outside))))
                 (#let view ({ty} (#ref #u64)) ({operator} (#get owner view)))
                 (#return (#deref view))\n"
        );
        check(&valid).unwrap();
        let invalid = valid
            .replace("((outside (#ref #u64)))", "((seed #u64))")
            .replace("((view outside))", "((view (#borrow seed)))");
        assert_local_return_escape(&invalid, "(#return (#deref view))", "seed");

        // The same load must retain an ordinary local's lifetime too, not only
        // distinguish the incoming reference from the by-value parameter slot.
        let local = invalid
            .replace("((seed #u64))", "()")
            .replace("(#let-mut owner", "(#let seed #u64 42u64) (#let-mut owner");
        assert_local_return_escape(&local, "(#return (#deref view))", "seed");
    }
}

#[test]
fn nested_owned_reference_loads_preserve_external_but_not_stack_origin() {
    for (declaration, ty, initializer, place) in [
        (
            "#struct Outer () ((padding #u64) (inner Holder))\n",
            "Outer",
            "(#struct-literal Outer ((padding 7u64) (inner (#struct-literal Holder ((view outside))))))",
            "(#get (#get owner inner) view)",
        ),
        (
            "",
            "(#tuple #u64 Holder)",
            "(#tuple (#tuple #u64 Holder) 7u64 (#struct-literal Holder ((view outside))))",
            "(#get (#get owner 1) view)",
        ),
        (
            "",
            "(#array Holder 2)",
            "(#array (#array Holder 2) (#struct-literal Holder ((view outside))) (#struct-literal Holder ((view outside))))",
            "(#get (#index owner 1usize) view)",
        ),
    ] {
        for (operator, handle) in [
            ("#borrow", "#ref"),
            ("#pin-borrow", "#pin-ref"),
            ("#borrow-mut", "#ref-mut"),
            ("#pin-borrow-mut", "#pin-ref-mut"),
        ] {
            let valid = format!(
                "#struct Holder () ((view (#ref #u64)))
 {declaration}
#fn read ((outside (#ref #u64))) (#ref #u64)
                     (#let-mut owner {ty} {initializer})
                     (#let view ({handle} (#ref #u64)) ({operator} {place}))
                     (#return (#deref view))\n"
            );
            check(&valid).unwrap();
            let invalid = valid
                .replace("((outside (#ref #u64)))", "((seed #u64))")
                .replace("(view outside)", "(view (#borrow seed))");
            assert_local_return_escape(&invalid, "(#return (#deref view))", "seed");
        }
    }
}

#[test]
fn by_value_parameter_slot_addresses_cannot_escape_but_incoming_referents_can() {
    for (parameter, place) in [("#u64", "owner"), ("Holder", "(#get owner view)")] {
        for (operator, handle) in [("#borrow", "#ref"), ("#pin-borrow", "#pin-ref")] {
            let pointee = if parameter == "#u64" {
                "#u64"
            } else {
                "(#ref #u64)"
            };
            let returned = format!("(#return ({operator} {place}))");
            let invalid = format!(
                "#struct Holder () ((view (#ref #u64)))
#fn read ((owner {parameter})) ({handle} {pointee}) {returned}\n"
            );
            assert_local_return_escape(&invalid, &returned, "owner");
        }
    }
    for (operator, handle) in [("#borrow", "#ref"), ("#pin-borrow", "#pin-ref")] {
        check(&format!(
            "#struct Holder () ((view (#ref #u64)))
#fn read ((owner Holder)) (#ref #u64)
                 (#let view ({handle} (#ref #u64)) ({operator} (#get owner view)))
                 (#return (#deref view))\n"
        ))
        .unwrap();
    }
    check(
        "#struct Holder () ((view (#ref-mut #u64)))
#fn read ((owner Holder)) (#ref-mut #u64) (#return (#get owner view))\n",
    )
    .unwrap();
}

#[test]
fn owned_projection_mutability_is_checked_at_the_root() {
    for operator in ["#borrow-mut", "#pin-borrow-mut"] {
        let source = format!(
            "#struct Owner () ((value #u64))
#fn main () ()
                 (#let owner Owner (#struct-literal Owner ((value 1u64))))
                 ({operator} (#get owner value)) (#return ())\n"
        );
        let error = diagnostic(&source);
        assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
        assert!(error.message.contains("immutable"), "{error:?}");
    }
}

#[test]
fn owned_projection_rejects_computed_temporary_roots() {
    for root in [
        "(#struct-literal Owner ((value 42u64)))",
        "(#call make ())",
        "(#block (#let temporary Owner (#struct-literal Owner ((value 42u64)))) temporary)",
    ] {
        let source = format!(
            "#struct Owner () ((value #u64))
#fn make () Owner (#return (#struct-literal Owner ((value 42u64))))
#fn main () () (#borrow (#get {root} value)) (#return ())\n"
        );
        let error = diagnostic(&source);
        assert_eq!(error.code, DiagnosticCode::Type, "{error:?}");
        assert!(error.message.contains("variable-rooted"), "{error:?}");
    }
}

#[test]
fn owned_projection_mutable_borrow_excludes_overlapping_access() {
    let source = "#struct Owner () ((value #u64))
#fn main () #u64
            (#let-mut owner Owner (#struct-literal Owner ((value 42u64))))
            (#let view (#ref-mut #u64) (#borrow-mut (#get owner value)))
            (#let conflicting #u64 (#get owner value))
            (#let result #u64 (#deref view))
            (#drop view) (#forget owner) (#return result)\n";
    let error = diagnostic(source);
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#get", "{error:?}");
    assert_eq!(
        span.start,
        source
            .find("(#let conflicting #u64 (#get owner value))")
            .unwrap()
            + "(#let conflicting #u64 (".len(),
        "{error:?}"
    );
    assert!(
        error
            .labels
            .iter()
            .any(|label| { &source[label.span.start..label.span.end] == "#borrow-mut" }),
        "{error:?}"
    );
}

#[test]
fn embedded_reference_crossing_requires_explicit_named_reborrow_root() {
    let source = "#struct Inner () ((value #u64))
#struct Owner () ((inner (#ref Inner)))
#fn main () ()
            (#let outside Inner (#struct-literal Inner ((value 42u64))))
            (#let-mut owner Owner (#struct-literal Owner ((inner (#borrow outside)))))
            (#borrow-mut (#get (#get owner inner) value)) (#return ())\n";
    let error = diagnostic(source);
    assert_eq!(error.code, DiagnosticCode::Type, "{error:?}");
    assert!(error.message.contains("embedded reference"), "{error:?}");
}
