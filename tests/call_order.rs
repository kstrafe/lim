mod support;

use std::{fs, process::Command, time::Duration};

const NEXT: &str = "
#fn next {
  #params = ((counter (#ref-mut #u64)) (expected #u64));
  #returns = #u64;
  #body = (
      (#assert (#u64::eq (#deref counter) expected))
      (#deref-set counter (#u64::add-wrap expected 1u64))
      (#return expected)\n  );\n}\n";

fn run(source: &str) {
    for source in [source.to_owned(), source.replace("#call ", "")] {
        let scratch = support::Scratch::new("call-order");
        let input = scratch.path().join("main.lim");
        let binary = scratch.path().join("program");
        fs::write(&input, &source).unwrap();
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
            Some(42),
            "{status:?}: {}",
            String::from_utf8_lossy(&stderr)
        );
    }
}

#[test]
fn integer_stack_calls_evaluate_once_in_written_order() {
    for count in [6, 7, 9, 32] {
        let parameters = (0..count)
            .map(|index| format!("(p{index} #u64)"))
            .collect::<Vec<_>>()
            .join(" ");
        let assertions = (0..count)
            .map(|index| format!("(#assert (#u64::eq p{index} {}u64))", count - index - 1))
            .collect::<Vec<_>>()
            .join("\n  ");
        // Written key order intentionally differs from declaration order.
        let arguments = (0..count)
            .rev()
            .map(|index| {
                format!(
                    "(p{index} (#call next ((counter (#borrow-mut counter)) (expected {}u64))))",
                    count - index - 1
                )
            })
            .collect::<Vec<_>>()
            .join(" ");
        run(&format!(
            "{NEXT}
#fn check {{
  #params = ({parameters});
  #returns = #u64;
  #body = ( {assertions} (#return 42u64)
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let-mut counter #u64 0u64)
              (#let result #u64 (#call check ({arguments})))
              (#assert (#u64::eq counter {count}u64))
              (#return result)\n  );\n}}\n"
        ));
    }
}

#[test]
fn multiword_stack_arguments_preserve_evaluation_and_word_order() {
    run(&format!(
        "{NEXT}
#struct Pair () ((first #u64) (second #u64))
#fn check {{
  #params = ((wide #u128) (pair Pair) (a #u64) (b #u64) (c #u64));
  #returns = #u64;
  #body = (
          (#assert (#u128::eq wide 18446744073709551627u128))
          (#assert (#u64::eq (#get pair first) 2u64))
          (#assert (#u64::eq (#get pair second) 1u64))
          (#assert (#u64::eq a 5u64))
          (#assert (#u64::eq b 4u64))
          (#assert (#u64::eq c 0u64))
          (#return 42u64)
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let result #u64 (#call check
            ((c (#call next ((counter (#borrow-mut counter)) (expected 0u64))))
             (pair (#struct-literal Pair
               ((second (#call next ((counter (#borrow-mut counter)) (expected 1u64))))
                (first (#call next ((counter (#borrow-mut counter)) (expected 2u64)))))))
             (wide (#u128::add-wrap
               (#as (#call next ((counter (#borrow-mut counter)) (expected 3u64))) #u128)
               18446744073709551624u128))
             (b (#call next ((counter (#borrow-mut counter)) (expected 4u64))))
             (a (#call next ((counter (#borrow-mut counter)) (expected 5u64)))))))
          (#assert (#u64::eq counter 6u64))
          (#return result)\n  );\n}}\n"
    ));
}

#[test]
fn nested_large_arguments_do_not_overwrite_previously_staged_values() {
    let fields = (0..8)
        .map(|index| format!("(f{index} #u64)"))
        .collect::<Vec<_>>()
        .join(" ");
    let value = |number| {
        format!(
            "(#struct-literal Large ({}))",
            (0..8)
                .rev()
                .map(|index| format!("(f{index} {number}u64)"))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    run(&format!(
        "#struct Large () ({fields})
#fn identity {{
  #params = ((value Large));
  #returns = Large;
  #body = ( (#return value)
  );
}}
#fn check {{
  #params = ((left Large) (right Large));
  #returns = #u64;
  #body = (
          (#assert (#u64::eq (#get left f7) 40u64))
          (#assert (#u64::eq (#get right f0) 2u64))
          (#return (#u64::add-wrap (#get left f0) (#get right f7)))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( (#return (#call check
          ((right {}) (left (#call identity ((value {})))))))\n  );\n}}\n",
        value(2),
        value(40)
    ));
}

#[test]
fn reversed_float_and_wide_intrinsics_keep_operand_roles_and_effects() {
    for ty in ["#f32", "#f64", "#u128", "#i128"] {
        run(&format!("{NEXT}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut counter #u64 0u64)
            (#let answer {ty} (#call {ty}::sub{}
              ((right (#block (#call next ((counter (#borrow-mut counter)) (expected 0u64))) (#as 2u64 {ty})))
               (left (#block (#call next ((counter (#borrow-mut counter)) (expected 1u64))) (#as 44u64 {ty}))))))
            (#assert (#call {ty}::eq ((right (#as 42u64 {ty})) (left answer))))
            (#assert (#u64::eq counter 2u64)) (#return 42u64)
  );\n}}\n", if ty.starts_with("#f") { "" } else { "-wrap" }));
    }
}
