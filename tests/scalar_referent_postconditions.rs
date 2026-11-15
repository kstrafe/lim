mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("scalar-referent-postconditions");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

const PROGRAM: &str = "#struct Holder () ((value (#ref #u64)))
#fn update {
  #params = ((selector (#ref-mut #u64)) (flag #bool));
  #returns = ();
  #body = (
      (#deref-set selector 1u64)
      (#if flag (#block (#return ())) ())
      (#deref-set selector 0u64)
      (#return ())
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
      (#let-mut selector #u64 0u64)
      (#let words (#array #u64 1) (#array-repeat 0u64))
      (#call update ((selector (#borrow-mut selector)) (flag false)))
      (#let answer #u64 (#match selector
        (#case 0 (#block
          (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
          (#let value #u64 (#deref (#get holder value)))
          (#forget holder) value))
        (#case _ 42u64)))
      (#forget words) (#return answer)\n  );\n}\n";

#[test]
fn fresh_pinned_heap_initializers_provide_only_current_scalar_facts() {
    let source = "#struct Holder () ((value (#ref #u64)))
#struct State () ((pc #u64))
#fn mode {
  #params = ((flag #bool));
  #returns = #u64;
  #body = ( (#return (#if flag 0u64 1u64))
  );
}
#fn inspect {
  #params = ((state (#pin-ref State)) (words (#slice #u64)));
  #returns = #u64;
  #body = (
          (#return (#match (#get state pc)
            (#case 0 42u64)
            (#case _ (#block
              (#let holder Holder (#unsafe (#word-read Holder words)))
              (#let answer #u64 (#deref (#get holder value)))
              (#forget holder) answer))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let pointer (#ptr-mut State) (#unsafe (#linux-syscall (#ptr-mut State)
            9usize (0usize (#size-of State) 3usize 34usize -1i64 0usize))))
          (#let initial State (#struct-literal State ((pc 0u64))))
          (#let-mut frame (#pin-own State) (#unsafe (#pin-own-of pointer initial)))
          (#let words (#array #u64 1) (#array-repeat 0u64))
          (#let answer #u64 (#call inspect ((state (#pin-own-borrow frame)) (words (#borrow-slice words)))))
          (#let raw (#ptr-mut State) (#unsafe (#pin-release frame)))
          (#let ignored #i64 (#unsafe (#linux-syscall #i64 11usize (raw (#size-of State)))))
          (#forget words) (#return answer)\n  );\n}\n";
    compile(source).expect("fresh heap state excludes the uninitialized reader");
    for initializer in ["1u64", "(#call mode ((flag true)))"] {
        let invalid = source.replace("(pc 0u64)", &format!("(pc {initializer})"));
        let error = compile(&invalid)
            .expect_err("selected or unknown heap states require actual reference initialization");
        assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    }
    let changed = source.replace(
        "(#let words",
        "(#let view (#pin-ref-mut State) (#pin-own-borrow-mut frame))
      (#unsafe (#pin-write (#pin-borrow-mut (#get view pc)) 1u64)) (#drop view)
      (#let words",
    );
    let error =
        compile(&changed).expect_err("a later alias write invalidates the initializer's selector");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn void_callee_referent_postcondition_excludes_inactive_word_reader() {
    let definite = PROGRAM
        .replace(
            "#fn update {\n  #params = ((selector (#ref-mut #u64)) (flag #bool));\n  #returns = ();\n  #body = (\n      (#deref-set selector 1u64)\n      (#if flag (#block (#return ())) ())\n      (#deref-set selector 0u64)\n      (#return ())\n  );\n}",
            "#fn update {\n  #params = ((selector (#ref-mut #u64)));\n  #returns = ();\n  #body = (\n      (#deref-set selector 1u64)\n      (#return ())\n  );\n}",
        )
        .replace("((selector (#borrow-mut selector)) (flag false))", "((selector (#borrow-mut selector)))");
    assert_ne!(definite, PROGRAM);
    compile(&definite).expect("the callee guarantees selector 1 on every normal return");
}

#[test]
fn alternate_normal_return_cannot_leave_a_stale_selector_postcondition() {
    let error = compile(PROGRAM)
        .expect_err("the alternate normal return writes selector 0, making the reader reachable");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn later_alias_mutation_invalidates_a_callee_selector_postcondition() {
    let source = PROGRAM
        .replace(
            "#fn main {\n  #params = ();\n  #returns = #u64;",
            "#fn mutate-alias {\n  #params = ((alias (#ref-mut #u64)));\n  #returns = ();\n  #body = (\n    (#deref-set alias 0u64)\n    (#return ())\n  );\n}\n#fn main {\n  #params = ();\n  #returns = #u64;",
        )
        .replace(
            "(#call update ((selector (#borrow-mut selector)) (flag false)))",
            "(#call update ((selector (#borrow-mut selector)) (flag true)))\n    (#call mutate-alias ((alias (#borrow-mut selector))))",
        );
    let error = compile(&source)
        .expect_err("a later mutation through an alias makes selector case 0 reachable");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}
