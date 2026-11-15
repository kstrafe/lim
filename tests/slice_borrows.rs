mod support;

use lim::{check_types, parse_program};
use std::{fs, os::unix::process::ExitStatusExt, process::Command};

const ARRAY: &str =
    "(#let-mut values (#array #u64 4) (#array-of (#array #u64 4) 1u64 2u64 3u64 4u64))";
fn checked(body: &str) -> Result<(), String> {
    check_types(&parse_program(&format!("#fn main () #u64 {ARRAY} {body}\n")).unwrap())
}
fn run(source: &str) -> std::process::Output {
    let scratch = support::Scratch::new("slice-borrows-native");
    let input = scratch.path().join("main.lim");
    let output = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let compiled = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&output)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    Command::new(output).output().unwrap()
}

#[test]
fn full_and_partial_direct_views_run_natively() {
    let source = format!(
        "#fn main () #u64 {ARRAY}
        (#let full (#slice #u64) (#borrow-slice values))
        (#let start #usize 1usize) (#let end #usize 3usize)
        (#let middle (#slice #u64) (#borrow-slice values start end))
        (#let empty (#slice #u64) (#borrow-slice values 4usize 4usize))
        (#assert (#usize::eq (#slice-len full) 4usize))
        (#assert (#usize::eq (#slice-len middle) 2usize))
        (#assert (#usize::eq (#slice-len empty) 0usize))
        (#return (#deref (#slice-idx middle 1usize)))\n"
    );
    assert_eq!(run(&source).status.code(), Some(3));
}

#[test]
fn constant_disjoint_mutable_borrows_can_coexist() {
    let body = "(#let left (#slice-mut #u64) (#borrow-slice-mut values 0usize 2usize))
      (#let right (#slice-mut #u64) (#borrow-slice-mut values 2usize 4usize))
      (#deref-set (#slice-mut-idx left 0usize) 17u64)
      (#deref-set (#slice-mut-idx right 0usize) 25u64)
      (#let answer #u64 (#u64::add-wrap (#deref (#slice-mut-idx left 0usize)) (#deref (#slice-mut-idx right 0usize))))
      (#forget left) (#forget right) (#return answer)";
    checked(body).unwrap();
    assert_eq!(
        run(&format!("#fn main () #u64 {ARRAY} {body}\n"))
            .status
            .code(),
        Some(42)
    );
}

#[test]
fn mixed_and_overlapping_ranges_conflict_but_disjoint_shared_range_is_valid() {
    for end in ["2usize", "3usize"] {
        let body = format!(
            "(#let left (#slice-mut #u64) (#borrow-slice-mut values 0usize {end}))
          (#let right (#slice-mut #u64) (#borrow-slice-mut values 1usize 4usize))
          (#forget left) (#forget right) (#return 0u64)"
        );
        assert!(checked(&body).unwrap_err().contains("borrow"));
    }
    let valid = "(#let left (#slice-mut #u64) (#borrow-slice-mut values 0usize 2usize))
      (#let right (#slice #u64) (#borrow-slice values 2usize 4usize))
      (#let answer #u64 (#deref (#slice-idx right 0usize)))
      (#forget left) (#return answer)";
    checked(valid).unwrap();
    assert!(checked(&valid.replace("values 2usize", "values 1usize"))
        .unwrap_err()
        .contains("borrow"));
}

#[test]
fn dynamic_ranges_are_conservative() {
    let body = "(#let boundary #usize 2usize)
      (#let left (#slice-mut #u64) (#borrow-slice-mut values 0usize boundary))
      (#let right (#slice-mut #u64) (#borrow-slice-mut values boundary 4usize))
      (#forget left) (#forget right) (#return 0u64)";
    assert!(checked(body).unwrap_err().contains("borrow"));
}

#[test]
fn mutable_subslice_suspends_parent_until_explicit_release() {
    let body = "(#let parent (#slice-mut #u64) (#borrow-slice-mut values))
      (#let child (#slice-mut #u64) (#slice-mut-range parent 1usize 3usize))
      (#deref-set (#slice-mut-idx child 0usize) 42u64)
      (#forget child)
      (#let answer #u64 (#deref (#slice-mut-idx parent 1usize)))
      (#forget parent) (#return answer)";
    checked(body).unwrap();
    assert_eq!(
        run(&format!("#fn main () #u64 {ARRAY} {body}\n"))
            .status
            .code(),
        Some(42)
    );
    let invalid = body.replace(
        "(#forget child)",
        "(#let count #usize (#slice-mut-len parent)) (#forget child)",
    );
    assert!(checked(&invalid).unwrap_err().contains("derived"));
}

#[test]
fn nested_subslices_and_sibling_reborrows_preserve_physical_offsets() {
    let body = "(#let parent (#slice-mut #u64) (#borrow-slice-mut values))
      (#let left (#slice-mut #u64) (#slice-mut-range parent 0usize 2usize))
      (#let right (#slice-mut #u64) (#slice-mut-range parent 2usize 4usize))
      (#let inner (#slice-mut #u64) (#slice-mut-range right 1usize 2usize))
      (#deref-set (#slice-mut-idx left 0usize) 17u64)
      (#deref-set (#slice-mut-idx inner 0usize) 25u64)
      (#forget inner) (#forget right) (#forget left) (#forget parent)
      (#return (#u64::add-wrap (#index values 0usize) (#index values 3usize)))";
    checked(body).unwrap();
    assert_eq!(
        run(&format!("#fn main () #u64 {ARRAY} {body}\n"))
            .status
            .code(),
        Some(42)
    );
}

#[test]
fn views_cannot_escape_owned_array_or_release_parent_early() {
    for (ty, creation) in [
        ("(#slice #u64)", "#borrow-slice"),
        ("(#slice-mut #u64)", "#borrow-slice-mut"),
    ] {
        let source =
            format!("#fn bad () {ty} {ARRAY} (#return ({creation} values 0usize 2usize))\n");
        let error = check_types(&parse_program(&source).unwrap()).unwrap_err();
        assert!(
            error.contains("local") || error.contains("escape"),
            "{error}"
        );
    }
    let body = "(#let parent (#slice-mut #u64) (#borrow-slice-mut values))
      (#let child (#slice-mut #u64) (#slice-mut-range parent 1usize 3usize))
      (#forget parent) (#forget child) (#return 0u64)";
    assert!(checked(body).unwrap_err().contains("reference"));
}

#[test]
fn immutable_places_non_arrays_wrong_bounds_and_wrong_slice_kind_are_rejected() {
    for body in [
        "(#let n #u64 2u64) (#let view (#slice #u64) (#borrow-slice n)) (#return 0u64)",
        "(#let view (#slice #u64) (#borrow-slice values 0u32 1usize)) (#return 0u64)",
        "(#let view (#slice #u64) (#borrow-slice values 0usize)) (#return 0u64)",
        "(#let view (#slice #u64) (#borrow-slice values)) (#let child (#slice-mut #u64) (#slice-mut-range view 0usize 1usize)) (#forget child) (#return 0u64)",
    ] { assert!(checked(body).is_err(), "{body}"); }
    let source = "#fn main () #u64 (#let values (#array #u64 1) (#array-of (#array #u64 1) 1u64))
        (#let view (#slice-mut #u64) (#borrow-slice-mut values)) (#forget view) (#return 0u64)\n";
    assert!(check_types(&parse_program(source).unwrap())
        .unwrap_err()
        .contains("immutable"));
}

#[test]
fn all_range_constructors_trap_on_invalid_bounds() {
    for bounds in ["3usize 2usize", "0usize 5usize", "5usize 5usize"] {
        for creator in ["#borrow-slice", "#borrow-slice-mut"] {
            let ty = if creator == "#borrow-slice" {
                "#slice"
            } else {
                "#slice-mut"
            };
            let source = format!(
                "#fn main () #u64 {ARRAY} (#let view ({ty} #u64) ({creator} values {bounds}))
                (#forget view) (#return 0u64)\n"
            );
            assert_eq!(run(&source).status.signal(), Some(4));
        }
        let source = format!("#fn main () #u64 {ARRAY} (#let parent (#slice-mut #u64) (#borrow-slice-mut values))
            (#let child (#slice-mut #u64) (#slice-mut-range parent {bounds})) (#forget child) (#forget parent) (#return 0u64)\n");
        assert_eq!(run(&source).status.signal(), Some(4));
    }
}

#[test]
fn direct_views_of_array_fields_return_through_helpers() {
    let source = "#struct Container () ((data (#array #u64 4)))
#fn shared ((source (#ref Container))) (#slice #u64)
          (#return (#borrow-slice (#get source data) 1usize 3usize))
#fn exclusive ((source (#ref-mut Container))) (#slice-mut #u64)
          (#return (#borrow-slice-mut (#get source data) 1usize 3usize))
#fn main () #u64
          (#let-mut owner Container (#struct-literal Container
            ((data (#array-of (#array #u64 4) 1u64 2u64 3u64 4u64)))))
          (#let view (#slice-mut #u64) (#call exclusive ((source (#borrow-mut owner)))))
          (#deref-set (#slice-mut-idx view 0usize) 42u64) (#forget view)
          (#let result (#slice #u64) (#call shared ((source (#borrow owner)))))
          (#let answer #u64 (#deref (#slice-idx result 0usize)))
          (#forget result) (#forget owner) (#return answer)\n";
    check_types(&parse_program(source).unwrap()).unwrap();
    assert_eq!(run(source).status.code(), Some(42));
    let invalid = source.replace(
        "(#forget result) (#forget owner)",
        "(#forget owner) (#forget result)",
    );
    assert!(check_types(&parse_program(&invalid).unwrap()).is_err());
}

#[test]
fn zero_length_and_zero_sized_element_arrays_can_be_borrowed() {
    for (element, length) in [("#u64", 0), ("()", 0), ("()", 3)] {
        let values = if length == 0 {
            String::new()
        } else {
            "() () ()".into()
        };
        let source = format!("#fn main () #u64
            (#let-mut values (#array {element} {length}) (#array-of (#array {element} {length}) {values}))
            (#let view (#slice {element}) (#borrow-slice values))
            (#assert (#usize::eq (#slice-len view) {length}usize)) (#forget view)
            (#let exclusive (#slice-mut {element}) (#borrow-slice-mut values 0usize {length}usize))
            (#assert (#usize::eq (#slice-mut-len exclusive) {length}usize)) (#forget exclusive)
            (#return 42u64)\n");
        assert_eq!(run(&source).status.code(), Some(42));
    }
}

#[test]
fn bounds_are_evaluated_once_in_start_end_order() {
    let source = format!("
#fn start ((counter (#ref-mut #u64))) #usize
          (#deref-set counter (#u64::add-wrap (#u64::mul-wrap (#deref counter) 10u64) 1u64)) (#return 1usize)
#fn end ((counter (#ref-mut #u64))) #usize
          (#deref-set counter (#u64::add-wrap (#u64::mul-wrap (#deref counter) 10u64) 2u64)) (#return 3usize)
#fn main () #u64 {ARRAY}
          (#let-mut count #u64 0u64)
          (#let view (#slice-mut #u64) (#borrow-slice-mut values
            (#call start ((counter (#borrow-mut count)))) (#call end ((counter (#borrow-mut count))))))
          (#assert (#u64::eq count 12u64))
          (#let child (#slice-mut #u64) (#slice-mut-range view 1usize 2usize))
          (#let answer #u64 (#deref (#slice-mut-idx child 0usize)))
          (#forget child) (#forget view) (#return answer)\n");
    assert_eq!(run(&source).status.code(), Some(3));
}

#[test]
fn mutable_range_reborrows_a_field_without_moving_it() {
    let source = format!(
        "#struct Holder () ((view (#slice-mut #u64)))
#fn main () #u64 {ARRAY}
          (#let-mut holder Holder (#struct-literal Holder ((view (#borrow-slice-mut values)))))
          (#let child (#slice-mut #u64) (#slice-mut-range (#get holder view) 1usize 3usize))
          (#deref-set (#slice-mut-idx child 0usize) 42u64) (#forget child)
          (#let count #usize (#slice-mut-len (#get holder view)))
          (#forget holder) (#return (#as count #u64))\n"
    );
    check_types(&parse_program(&source).unwrap()).unwrap();
    assert_eq!(run(&source).status.code(), Some(4));
}

#[test]
fn slice_field_parent_is_suspended_and_sibling_fields_remain_usable() {
    let source = format!(
        "#struct Holder () ((view (#slice-mut #u64)) (other (#slice-mut #u64)))
#fn main () #u64 {ARRAY}
             (#let-mut holder Holder (#struct-literal Holder
               ((view (#borrow-slice-mut values 0usize 2usize))
                (other (#borrow-slice-mut values 2usize 4usize)))))
             (#let child (#slice-mut #u64) (#slice-mut-range (#get holder view) 0usize 1usize))
             (#deref-set (#slice-mut-idx child 0usize) 40u64)
             (#let other-child (#slice-mut #u64) (#slice-mut-range (#get holder other) 0usize 1usize))
             (#deref-set (#slice-mut-idx other-child 0usize) 2u64)
             (#let answer #u64 (#u64::add-wrap (#deref (#slice-mut-idx child 0usize))
               (#deref (#slice-mut-idx other-child 0usize))))
             (#forget child) (#forget other-child) (#forget holder) (#return answer)\n"
    );
    check_types(&parse_program(&source).unwrap()).unwrap();
    assert_eq!(run(&source).status.code(), Some(42));
    for access in [
        "(#let count #usize (#slice-mut-len (#get holder view)))",
        "(#forget (#get holder view))",
        "(#forget holder)",
    ] {
        let bad = source.replace("(#forget child)", &format!("{access} (#forget child)"));
        assert!(
            check_types(&parse_program(&bad).unwrap()).is_err(),
            "{access}"
        );
    }
}

#[test]
fn slice_field_reborrowing_rejects_shared_and_temporary_receivers() {
    let source = format!(
        "#struct Holder () ((view (#slice-mut #u64)))
#fn main () #u64 {ARRAY}
             (#let holder Holder (#struct-literal Holder ((view (#borrow-slice-mut values)))))
             (#let child (#slice-mut #u64) (#slice-mut-range (#get holder view) 0usize 1usize))
             (#forget child) (#forget holder) (#return 0u64)\n"
    );
    assert!(check_types(&parse_program(&source).unwrap())
        .unwrap_err()
        .contains("exclusive"));
    let temporary = source.replace(
        "(#get holder view)",
        "(#if #true (#get holder view) (#get holder view))",
    );
    assert!(check_types(&parse_program(&temporary).unwrap()).is_err());
}

#[test]
fn returned_slice_field_reborrow_retains_its_owner_and_nested_offset() {
    let source = format!(
        "#struct Holder () ((view (#slice-mut #u64)))
#fn middle ((source (#ref-mut Holder))) (#slice-mut #u64)
             (#return (#slice-mut-range (#get source view) 1usize 3usize))
#fn main () #u64 {ARRAY}
             (#let-mut holder Holder (#struct-literal Holder ((view (#borrow-slice-mut values)))))
             (#let child (#slice-mut #u64) (#call middle ((source (#borrow-mut holder)))))
             (#let nested (#slice-mut #u64) (#slice-mut-range child 1usize 2usize))
             (#deref-set (#slice-mut-idx nested 0usize) 42u64)
             (#forget nested) (#forget child)
             (#let answer #u64 (#deref (#slice-mut-idx (#get holder view) 2usize)))
             (#forget holder) (#return answer)\n"
    );
    check_types(&parse_program(&source).unwrap()).unwrap();
    assert_eq!(run(&source).status.code(), Some(42));
    for action in ["(#forget holder)", "(#set-index values 0usize 5u64)"] {
        let bad = source.replace("(#forget nested)", &format!("{action} (#forget nested)"));
        assert!(check_types(&parse_program(&bad).unwrap()).is_err());
    }
    let shared = source.replace("(#ref-mut Holder)", "(#ref Holder)");
    assert!(check_types(&parse_program(&shared).unwrap()).is_err());
}

#[test]
fn nested_tuple_slice_handles_reborrow_and_prevent_parent_moves() {
    let source = format!(
        "#struct Holder () ((pair (#tuple #u64 (#slice-mut #u64))))
#fn main () #u64 {ARRAY}
             (#let-mut holder Holder (#struct-literal Holder
               ((pair (#tuple (#tuple #u64 (#slice-mut #u64)) 7u64 (#borrow-slice-mut values))))))
             (#let child (#slice-mut #u64) (#slice-mut-range (#get (#get holder pair) 1) 1usize 3usize))
             (#let sibling #u64 (#get (#get holder pair) 0))
             (#deref-set (#slice-mut-idx child 0usize) 35u64)
             (#let answer #u64 (#u64::add-wrap sibling (#deref (#slice-mut-idx child 0usize))))
             (#forget child) (#forget holder) (#return answer)\n"
    );
    check_types(&parse_program(&source).unwrap()).unwrap();
    assert_eq!(run(&source).status.code(), Some(42));
    let bad = source.replace(
        "(#forget child)",
        "(#forget (#get holder pair)) (#forget child)",
    );
    assert!(check_types(&parse_program(&bad).unwrap()).is_err());
}

#[test]
fn bound_effects_cannot_consume_backing_storage() {
    for creator in ["#borrow-slice", "#borrow-slice-mut"] {
        let slice_type = if creator == "#borrow-slice" {
            "#slice"
        } else {
            "#slice-mut"
        };
        let index = if creator == "#borrow-slice" {
            "#slice-idx"
        } else {
            "#slice-mut-idx"
        };
        let source = format!("#struct Token (#linear) ((value #u64))
#fn consume ((input (#array Token 1))) #usize (#forget input) (#return 0usize)
#fn main () #u64
              (#let-mut values (#array Token 1) (#array-of (#array Token 1) (#struct-literal Token ((value 42u64)))))
              (#let view ({slice_type} Token) ({creator} values (#call consume ((input values))) 1usize))
              (#let answer #u64 (#get ({index} view 0usize) value)) (#forget view) (#return answer)\n");
        let error = check_types(&parse_program(&source).unwrap()).unwrap_err();
        assert!(
            error.contains("consumed")
                || error.contains("borrow")
                || error.contains("used more than once"),
            "{error}"
        );
    }
}

#[test]
fn direct_slice_borrow_cannot_erase_a_pinned_projection() {
    let source = "#struct Container () ((data (#array #u64 2)))
#fn bad ((source (#pin-ref-mut Container))) (#slice-mut #u64)
          (#return (#borrow-slice-mut (#get source data)))\n";
    assert!(check_types(&parse_program(source).unwrap())
        .unwrap_err()
        .contains("pinning"));
}

#[test]
fn aggregate_elements_use_their_full_storage_stride() {
    let source = "#struct Pair () ((left #u64) (right #u64))
#fn main () #u64
          (#let-mut values (#array Pair 3) (#array-of (#array Pair 3)
            (#struct-literal Pair ((left 1u64) (right 2u64)))
            (#struct-literal Pair ((left 3u64) (right 4u64)))
            (#struct-literal Pair ((left 5u64) (right 6u64)))))
          (#let view (#slice-mut Pair) (#borrow-slice-mut values 1usize 3usize))
          (#let item (#ref-mut Pair) (#slice-mut-idx view 1usize))
          (#deref-set (#borrow-mut (#get item right)) 42u64) (#forget item) (#forget view)
          (#let shared (#slice Pair) (#borrow-slice values 2usize 3usize))
          (#let answer #u64 (#get (#slice-idx shared 0usize) right))
          (#forget shared) (#forget values) (#return answer)\n";
    assert_eq!(run(source).status.code(), Some(42));
}

#[test]
fn reference_elements_preserve_selected_referent_lifetimes() {
    let source = "#fn first ((source (#slice (#ref #u64)))) (#ref #u64)
          (#return (#deref (#slice-idx source 0usize)))
#fn main () #u64
          (#let-mut left #u64 1u64) (#let-mut right #u64 42u64)
          (#let values (#array (#ref #u64) 2)
            (#array-of (#array (#ref #u64) 2) (#borrow left) (#borrow right)))
          (#let selected (#ref #u64) (#call first ((source (#borrow-slice values 1usize 2usize)))))
          (#forget values) (#set left 2u64) (#return (#deref selected))\n";
    check_types(&parse_program(source).unwrap()).unwrap();
    assert_eq!(run(source).status.code(), Some(42));
    let invalid = source.replace("(#set left 2u64)", "(#set right 2u64)");
    assert!(check_types(&parse_program(&invalid).unwrap())
        .unwrap_err()
        .contains("borrow"));
}
