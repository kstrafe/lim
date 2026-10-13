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

const PROGRAM: &str = "(#struct Holder (: value (#ref #u64)))
  (#fn update (: selector (#ref-mut #u64) : flag #bool) ()
    (#deref-set selector 1u64)
    (#if flag (#block (#return ())) ())
    (#deref-set selector 0u64)
    (#return ()))
  (#fn main () #u64
    (#let-mut selector #u64 0u64)
    (#let words (#array #u64 1) (#array-repeat 0u64))
    (#call update (: selector (#borrow-mut selector) : flag false))
    (#let answer #u64 (#match selector
      (#case 0 (#block
        (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let value #u64 (#deref (#get holder value)))
        (#forget holder) value))
      (#case _ 42u64)))
    (#forget words) (#return answer))";

#[test]
fn void_callee_referent_postcondition_excludes_inactive_word_reader() {
    let definite = PROGRAM
        .replace(
            "(#fn update (: selector (#ref-mut #u64) : flag #bool) ()\n    (#deref-set selector 1u64)\n    (#if flag (#block (#return ())) ())\n    (#deref-set selector 0u64)\n    (#return ()))",
            "(#fn update (: selector (#ref-mut #u64)) ()\n    (#deref-set selector 1u64)\n    (#return ()))",
        )
        .replace("(: selector (#borrow-mut selector) : flag false)", "(: selector (#borrow-mut selector))");
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
            "  (#fn main () #u64",
            "  (#fn mutate-alias (: alias (#ref-mut #u64)) ()\n    (#deref-set alias 0u64)\n    (#return ()))\n  (#fn main () #u64",
        )
        .replace(
            "(#call update (: selector (#borrow-mut selector) : flag false))",
            "(#call update (: selector (#borrow-mut selector) : flag true))\n    (#call mutate-alias (: alias (#borrow-mut selector)))",
        );
    let error = compile(&source)
        .expect_err("a later mutation through an alias makes selector case 0 reachable");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}
