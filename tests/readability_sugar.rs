mod support;

use std::{process::Command, time::Duration};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("readability-sugar");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn borrowed_arguments_and_generated_case_sequences_run_in_order() {
    let source = r#"
#gn make-function (name)
          `((#fn ,name ((value (#ref-mut #u64))) #u64
              (#return (#match true
                (#case true (#when true)
                  (#deref-set value (#u64::add-wrap (#deref value) 1u64))
                  (#deref-set value (#u64::add-wrap (#deref value) 1u64))
                  (#deref value))
                (#case _ 0u64)))))
#generate make-function increment
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut value #u64 40u64)
          (#return (#call increment (($ (#borrow-mut value)))))
  );
}
    "#;
    let assembly = compile(source).unwrap();
    let scratch = support::Scratch::new("readability-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

#[test]
fn shorthand_keeps_mutability_and_type_errors_on_the_original_expression() {
    for (binding, ty, operation) in [
        ("#let", "#u64", "#borrow-mut"),
        ("#let-mut", "#u32", "#borrow-mut"),
        ("#let-mut", "#u64", "#borrow"),
    ] {
        let source = format!(
            "#fn take {{
  #params = ((value (#ref-mut #u64)));
  #returns = ();
  #body = ( (#return ())
  );
}}
#fn main {{
  #params = ();
  #returns = ();
  #body = ( ({binding} value {ty} 42{})
              (#call take (($ ({operation} value)))) (#return ())\n  );\n}}\n",
            &ty[1..]
        );
        let error = compile(&source).expect_err("sugar must not infer a type or borrow mode");
        let span = error.span.expect("original source must be highlighted");
        let line = source[..span.start]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count();
        let expected_line = source
            .lines()
            .position(|line| line.contains("#call take"))
            .expect("the shorthand argument is written at the take call");
        assert_eq!(line, expected_line, "{error:?}");
    }
}

#[test]
fn case_sequences_do_not_hide_aliasing_or_linear_leaks() {
    for body in [
        "(#let held (#ref #u64) (#borrow value)) (#set value 0u64) (#deref held)",
        "(#let leaked Token (#struct-literal Token ())) 42u64",
    ] {
        let source = format!(
            "#struct Token (#linear) ()
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut value #u64 42u64)
              (#return (#match true (#case true {body}) (#case false 0u64)))\n  );\n}}\n"
        );
        compile(&source).expect_err("ordinary ownership checks must apply to case sequences");
    }
}

#[test]
fn formatting_preserves_comments_sugar_and_semantics() {
    let source = "#fn take {
  #params = ((value (#ref #u64)));
  #returns = #u64;
  #body = ( (#return (#deref value))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let value #u64 42u64)
          (#return (#match true
            (#case true // keep this arm comment
              (#let answer #u64 (#call take (($ (#borrow value))))) answer)
            (#case false 0u64)))\n  );\n}\n";
    let formatted = lim::format_source(source).unwrap();
    assert!(formatted.contains("// keep this arm comment\n"));
    assert!(formatted.contains("($ (#borrow value))"));
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
    assert_eq!(compile(source).unwrap(), compile(&formatted).unwrap());
}
