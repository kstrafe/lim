mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("heap-word-transfers");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

const SOURCE: &str = "#struct Holder () ((link (#ref #u64)))
#struct Frame () ((state #u64) (original (#array #u64 1)) (moved (#array #u64 1)))
#fn relay {
  #params = ((frame Frame) (transfer #bool));
  #returns = Frame;
  #body = (
      (#let-mut result Frame frame)
      (#match (#get result state)
        (#case 1 (#if transfer (#block
          (#let owner (#pin-own Holder)
            (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get result original)))))
          (#unsafe (#word-write (#pin-own Holder) (#borrow-slice-mut (#get result moved)) owner))
          (#set-field result state 2u64)) ()))
        (#case _ (#unreachable)))
      (#return result)
  );
}
#fn read {
  #params = ((frame Frame));
  #returns = #u64;
  #body = (
      (#let-mut local Frame frame)
      (#let owner (#pin-own Holder) (#match (#get local state)
        (#case 1 (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get local original)))))
        (#case 2 (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get local moved)))))
        (#case _ (#unreachable))))
      (#let view (#pin-ref Holder) (#pin-own-borrow (#borrow owner)))
      (#let answer #u64 (#deref (#get view link))) (#forget view)
      (#let pointer (#ptr-mut Holder) (#unsafe (#pin-release owner)))
      (#forget pointer) (#forget local) (#return answer)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
      (#let-mut amount #u64 42u64)
      (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
        (0usize 4096usize 3usize 34usize -1i64 0usize))))
      (#let-mut frame Frame (#struct-literal Frame
        ((state 1u64) (original (#array-repeat 0u64)) (moved (#array-repeat 0u64)))))
      (#unsafe (#word-write (#pin-own Holder) (#borrow-slice-mut (#get frame original))
        (#pin-own-of pointer (#struct-literal Holder ((link (#borrow amount)))))))
      (#let forwarded Frame (#call relay ((frame frame) (transfer #false))))
      (#let answer #u64 (#call read ((frame forwarded))))
      (#set amount 0u64) (#return answer)\n  );\n}\n";

#[test]
fn conditional_pass_through_preserves_heap_owner_and_retained_reference() {
    compile(SOURCE).expect("a pass-through return preserves the checked heap-entry loan");
    compile(&SOURCE.replace("(transfer #false)", "(transfer #true)"))
        .expect("a checked typed word transfer carries the pointee loan to the destination");
}

#[test]
fn heap_word_transfer_keeps_the_original_referent_borrowed() {
    let invalid = SOURCE.replace(
        "(#let answer #u64 (#call read",
        "(#set amount 0u64) (#let answer #u64 (#call read",
    );
    let error = compile(&invalid).expect_err("the heap retains amount until its owner is consumed");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn retired_heap_word_cells_cannot_supply_a_transfer() {
    let invalid = SOURCE.replace(
        "(#let forwarded Frame",
        "(#unsafe (#word-forget (#pin-own Holder) (#borrow-slice-mut (#get frame original))))
         (#let forwarded Frame",
    );
    let error = compile(&invalid).expect_err("retired owner metadata cannot be restored by relay");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn pointer_bytes_cannot_replace_a_heap_owners_retained_loan() {
    let invalid = SOURCE.replace(
        "(#let forwarded Frame",
        "(#unsafe (#word-write #u64 (#borrow-slice-mut (#get frame original)) 0u64))
         (#let forwarded Frame",
    );
    let error =
        compile(&invalid).expect_err("plain bytes do not initialize an owning reference slot");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}
