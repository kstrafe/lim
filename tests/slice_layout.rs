mod support;

use std::{fs, process::Command, time::Duration};

fn native_exit(source: &str, expected: i32, case: &str) {
    let scratch = support::Scratch::new("slice-layout");
    let source_path = scratch.path().join("case.lim");
    let binary_path = scratch.path().join("case");
    fs::write(&source_path, source).expect("write Lim source");

    let (status, _, errors) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source_path)
            .arg("-o")
            .arg(&binary_path),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap_or_else(|error| panic!("{case}: compile: {error}"));
    assert!(
        status.success(),
        "{case}: compiler/linker failed: {status}\n{}",
        String::from_utf8_lossy(&errors)
    );

    let (status, _, errors) = support::run(
        &mut Command::new(&binary_path),
        Duration::from_secs(2),
        1024 * 1024,
    )
    .unwrap_or_else(|error| panic!("{case}: runtime: {error}"));
    assert_eq!(
        status.code(),
        Some(expected),
        "{case}: unexpected result; stderr: {}",
        String::from_utf8_lossy(&errors)
    );
}

#[test]
fn large_array_dereference_returns_preserve_local_static_and_pinned_layout() {
    let array = "(#array #u64 8)";
    let values = "(#array-of (#array #u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 42u64)";
    for (case, declarations, reference, argument) in [
        (
            "local",
            format!("(#let values {array} {values})"),
            "#ref",
            "(#borrow values)",
        ),
        (
            "pinned",
            format!("(#let values {array} {values})"),
            "#pin-ref",
            "(#pin-borrow values)",
        ),
        (
            "static",
            String::new(),
            "#ref",
            "(#unsafe (#borrow global-values))",
        ),
    ] {
        let source = format!(
            "#static global-values {array} {values}
#fn snapshot {{
  #params = ((values ({reference} {array})));
  #returns = {array};
  #body = (
              (#return (#deref values))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( {declarations}
              (#let copied {array} (#call snapshot ((values {argument}))))
              (#assert (#u64::eq (#index copied 0usize) 1u64))
              (#return (#index copied 7usize))\n  );\n}}\n"
        );
        native_exit(&source, 42, case);
    }
}

#[test]
fn large_string_array_payloads_use_aggregate_destinations() {
    native_exit(
        r#"
#enum Message () ((Message.Text (#array #char 14)))
#fn message {
  #params = ();
  #returns = Message;
  #body = ( (#return (Message.Text "abcdefghijklm*"))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#return (#match (#call message ())
            (#case (Message.Text characters) (#as (#index characters 13usize) #u64))))
  );
}
    "#,
        42,
        "large string array payload",
    );
}

#[test]
fn local_array_borrow_to_slice_in_helper() {
    native_exit(
        r#"
#fn read-third {
  #params = ((values (#ref (#array #u64 3))));
  #returns = #u64;
  #body = (
    (#let view (#slice #u64) (#slice-of values))
    (#let range (#slice #u64) (#slice-range view 1usize 3usize))
    (#return (#deref (#slice-idx range 1usize)))
  );
}

#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let values (#array #u64 3)
      (#array-of (#array #u64 3) 10u64 20u64 42u64))
    (#return (#call read-third ((values (#borrow values)))))
  );
}
"#,
        42,
        "local array borrow to slice in helper",
    );
}

#[test]
fn static_array_borrow_to_slice_in_helper() {
    native_exit(
        r#"
#static global-values (#array #u64 3)
    (#array-of (#array #u64 3) 10u64 20u64 42u64)

#fn read-third {
  #params = ((values (#ref (#array #u64 3))));
  #returns = #u64;
  #body = (
    (#let view (#slice #u64) (#slice-of values))
    (#return (#deref (#slice-idx view 2usize)))
  );
}

#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#return (#unsafe
      (#call read-third ((values (#borrow global-values))))))
  );
}
"#,
        42,
        "static array borrow to slice in helper",
    );
}

#[test]
fn range_and_index_preserve_slice_layout_across_calls() {
    native_exit(
        r#"
#fn middle {
  #params = ((values (#slice #u64)));
  #returns = #u64;
  #body = (
    (#let range (#slice #u64) (#slice-range values 1usize 3usize))
    (#return (#deref (#slice-idx range 1usize)))
  );
}

#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let values (#array #u64 4)
      (#array-of (#array #u64 4) 5u64 10u64 42u64 80u64))
    (#let view (#slice #u64) (#slice-of (#borrow values)))
    (#return (#call middle ((values view))))
  );
}
"#,
        42,
        "slice range and index across calls",
    );
}

#[test]
fn mutable_slice_split_and_index_preserve_layout_across_calls() {
    native_exit(
        r#"
#fn update-halves {
  #params = ((whole (#slice-mut #u64)));
  #returns = #u64;
  #body = (
    (#let (#tuple left right)
      (#tuple (#slice-mut #u64) (#slice-mut #u64))
      (#slice-mut-split whole 2usize))
    (#deref-set (#slice-mut-idx left 1usize) 20u64)
    (#deref-set (#slice-mut-idx right 0usize) 22u64)
    (#let left-value #u64 (#deref (#slice-mut-idx left 1usize)))
    (#let right-value #u64 (#deref (#slice-mut-idx right 0usize)))
    (#forget left)
    (#forget right)
    (#return (#u64::add-wrap
      left-value right-value))
  );
}

#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let-mut values (#array #u64 4)
      (#array-of (#array #u64 4) 1u64 2u64 3u64 4u64))
    (#let whole (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
    (#return (#call update-halves ((whole whole))))
  );
}
"#,
        42,
        "mutable slice split across calls",
    );
}

#[test]
fn multiword_slice_mutation_and_read_preserve_element_address() {
    native_exit(
        r#"
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
    (#let-mut values (#array (#tuple #u64 #u64 #u64) 2)
      (#array-of (#array (#tuple #u64 #u64 #u64) 2)
        (#tuple (#tuple #u64 #u64 #u64) 10u64 20u64 30u64)
        (#tuple (#tuple #u64 #u64 #u64) 30u64 12u64 1u64)))
    (#let whole (#slice-mut (#tuple #u64 #u64 #u64))
      (#slice-mut-of (#borrow-mut values)))
    (#deref-set (#slice-mut-idx whole 1usize)
      (#tuple (#tuple #u64 #u64 #u64) 40u64 1u64 1u64))
    (#forget whole)
    (#let view (#slice (#tuple #u64 #u64 #u64))
      (#slice-of (#borrow values)))
    (#let item (#tuple #u64 #u64 #u64) (#deref (#slice-idx view 1usize)))
    (#return (#u64::add-wrap (#u64::add-wrap (#get item 0) (#get item 1)) (#get item 2)))
  );
}
"#,
        42,
        "multiword slice mutation and read",
    );
}
