mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("pinned-extraction-footprints");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn pinned_extraction_from_disjoint_word_cell_preserves_neighbor_source() {
    let source = "#struct Holder () ((value (#ref #u64)))
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
          (#let amount #u64 42u64)
          (#let-mut words (#array #u64 2) (#array-repeat 0u64))
          (#unsafe (#word-write Holder (#borrow-slice-mut words 0usize 1usize)
            (#struct-literal Holder ((value (#borrow amount))))))
          (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)
            (#struct-literal Holder ((value (#borrow amount))))))
          (#let extracted Holder (#unsafe (#pin-read
            (#unsafe (#word-view (#pin-ref-mut Holder)
              (#borrow-slice-mut words 0usize 1usize))))))
          (#forget extracted)
          (#let neighbor Holder (#unsafe (#word-read Holder (#borrow-slice words 1usize 2usize))))
          (#let answer #u64 (#deref (#get neighbor value)))
          (#forget neighbor) (#forget words) (#return answer)\n  );\n}\n";
    compile(source).expect("extracting cell zero leaves cell one's source loan intact");
}

#[test]
fn pinned_extraction_does_not_initialize_a_disjoint_word_cell() {
    let source = "#struct Holder () ((value (#ref #u64)))
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
          (#let amount #u64 42u64)
          (#let-mut words (#array #u64 2) (#array-repeat 0u64))
          (#unsafe (#word-write Holder (#borrow-slice-mut words 0usize 1usize)
            (#struct-literal Holder ((value (#borrow amount))))))
          (#let extracted Holder (#unsafe (#pin-read
            (#unsafe (#word-view (#pin-ref-mut Holder)
              (#borrow-slice-mut words 0usize 1usize))))))
          (#forget extracted)
          (#let neighbor Holder (#unsafe (#word-read Holder (#borrow-slice words 1usize 2usize))))
          (#let answer #u64 (#deref (#get neighbor value)))
          (#forget neighbor) (#forget words) (#return answer)\n  );\n}\n";
    let error =
        compile(&source).expect_err("extracting cell zero cannot fabricate cell one's source loan");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn cloning_a_builtin_raw_pointer_preserves_disjoint_selector_facts() {
    let source = "#struct Holder () ((value (#ref #u64)))
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
          (#let-mut selector #u64 0u64)
          (#let-mut unrelated #u64 7u64)
          (#let pointer (#ptr-mut #u64) (#unsafe (#ref-ptr (#borrow-mut unrelated))))
          (#let copied (#ptr-mut #u64) (#clone pointer))
          (#let words (#array #u64 1) (#array-repeat 0u64))
          (#let answer #u64 (#match selector
            (#case 1 (#block
              (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
              (#let value #u64 (#deref (#get holder value)))
              (#forget holder) value))
            (#case _ 42u64)))
          (#forget copied) (#forget words) (#return answer)\n  );\n}\n";
    compile(source).expect("copying a raw pointer has no arbitrary pointee write effect");
}

#[test]
fn custom_clone_through_a_raw_pointer_invalidates_selector_facts() {
    let source = "#struct Holder () ((value (#ref #u64)))
#struct Payload () ((target (#ptr-mut #u64)))
#fn Payload::clone {
  #params = ((value Payload));
  #returns = Payload;
  #effects = (#global-access #io); #body = (
          (#unsafe (#ptr-write (#get value target) 1u64)) (#return value)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io (#effects-of Payload::clone)); #body = (
          (#let-mut selector #u64 0u64)
          (#let payload Payload (#struct-literal Payload
            ((target (#ref-ptr (#borrow-mut selector))))))
          (#let copied Payload (#clone payload))
          (#let words (#array #u64 1) (#array-repeat 0u64))
          (#let answer #u64 (#match selector
            (#case 1 (#block
              (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
              (#let value #u64 (#deref (#get holder value)))
              (#forget holder) value))
            (#case _ 42u64)))
          (#forget copied) (#forget words) (#return answer)\n  );\n}\n";
    let error = compile(source)
        .expect_err("an opaque user clone may mutate the selector through its pointer");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

const RETURNED_FRAME: &str = "#struct Holder () ((value (#ref #u64)))
#struct Frame () ((state #u64) (words (#array #u64 1)))
#fn make {
  #params = ((value (#ref #u64)) (flag #bool));
  #returns = Frame;
  #effects = (#global-access #io); #body = (
      (#let-mut frame Frame (#struct-literal Frame
        ((state 0u64) (words (#array-repeat 0u64)))))
      (#if flag (#block
        (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
          (#struct-literal Holder ((value value)))))
        (#set-field frame state 1u64)) ())
      (#return frame)
  );
}
#fn observe {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#fn read {
  #params = ((frame Frame));
  #returns = #u64;
  #effects = (#global-access #io); #body = (
      (#loop (#match (#get frame state)
        (#case 1 (#block
          (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
          (#let answer #u64 (#deref (#get holder value)))
          (#forget holder) (#forget frame) (#return answer)))
        (#case _ (#block (#forget frame) (#return 42u64)))))
      (#return 0u64)\n  );\n}\n";

#[test]
fn pure_disjoint_read_preserves_returned_conditional_word_guarantee() {
    let source = format!(
        "{RETURNED_FRAME}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut frame Frame (#struct-literal Frame
               ((state 0u64) (words (#array-repeat 0u64)))))
             (#let observed #u64 (#call observe ((value 7u64))))
             (#let answer #u64 (#call read ((frame frame))))
             (#return (#u64::add-wrap answer observed))\n  );\n}}\n"
    );
    compile(&source).expect("a proven read-only disjoint call preserves the returned guarantee");
}

#[test]
fn opaque_raw_write_revokes_returned_conditional_word_guarantee() {
    let source = format!(
        "{RETURNED_FRAME}
#fn opaque-write {{
  #params = ((target (#ptr-mut #u64)));
  #returns = ();
  #effects = (#global-access #io); #body = (
             (#unsafe (#ptr-write target 0u64)) (#return ())
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of make) (#effects-of opaque-write)); #body = (
             (#let value #u64 42u64)
             (#let-mut frame Frame (#call make ((value (#borrow value)) (flag true))))
             (#let target (#ptr-mut #u64)
               (#unsafe (#ref-ptr (#borrow-mut (#index (#get frame words) 0usize)))))
             (#call opaque-write ((target target)))
             (#forget target)
             (#let answer #u64 (#call read ((frame frame))))
             (#return answer)\n  );\n}}\n"
    );
    let error = compile(&source)
        .expect_err("an opaque byte write may destroy the initialized reference cell");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn word_forget_alias_revokes_returned_conditional_word_guarantee() {
    let source = format!(
        "{RETURNED_FRAME}
#fn retire {{
  #params = ((words (#slice-mut #u64)));
  #returns = ();
  #effects = (#global-access #io); #body = (
             (#unsafe (#word-forget Holder words)) (#return ())
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of make) (#effects-of retire)); #body = (
             (#let value #u64 42u64)
             (#let-mut frame Frame (#call make ((value (#borrow value)) (flag true))))
             (#call retire ((words (#borrow-slice-mut (#get frame words)))))
             (#let answer #u64 (#call read ((frame frame))))
             (#return answer)\n  );\n}}\n"
    );
    let error = compile(&source)
        .expect_err("a summarized word-forget through an alias retires the conditional loan");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn absent_owned_enum_payload_does_not_create_a_nested_write_footprint() {
    let source = "#struct Holder () ((value (#ref #u64)))
#struct Frame () ((state #u64) (words (#array #u64 1)))
#struct Container () ((target (#ref-mut #u64)))
#enum Handle () ((Handle.Empty) (Handle.Full (#ref-mut Container)))
#fn empty {
  #params = ();
  #returns = Handle;
  #body = ( (#return (Handle.Empty))
  );
}
#fn mutate {
  #params = ((handle Handle));
  #returns = ();
  #body = (
          (#match handle
            (#case (Handle.Empty) ())
            (#case (Handle.Full container) (#block
              (#deref-set (#get container target) 1u64) (#forget container) ())))
          (#return ())
  );
}
#fn read {
  #params = ((frame (#ref Frame)));
  #returns = #u64;
  #effects = (#global-access #io); #body = (
          (#return (#match (#get frame state)
            (#case 0 42u64)
            (#case _ (#block
              (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
              (#let answer #u64 (#deref (#get holder value)))
              (#forget holder) answer))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of read)); #body = (
          (#let-mut frame Frame (#struct-literal Frame ((state 0u64) (words (#array-repeat 0u64)))))
          (#call mutate ((handle (#call empty ()))))
          (#let-mut unrelated #u64 0u64)
          (#let-mut container Container (#struct-literal Container ((target (#borrow-mut unrelated)))))
          (#call mutate ((handle (Handle.Full (#borrow-mut container)))))
          (#forget container)
          (#let answer #u64 (#call read ((frame (#borrow frame)))))
          (#forget frame) (#return answer)\n  );\n}\n";
    compile(source).expect(
        "an absent owned payload contributes no nested address, preserving the state-zero reader guard",
    );

    let invalid = source.replace(
        "(#borrow-mut unrelated)",
        "(#borrow-mut (#get frame state))",
    );
    let error = compile(&invalid).expect_err(
        "an inhabited payload with a real target can activate the uninitialized reader",
    );
    assert!(
        error.message.contains("input loan") || error.message.contains("unresolved"),
        "{error:?}"
    );
}

const CONDITIONAL_SCALAR_OUTCOME: &str = "#struct Holder () ((value (#ref #u64)))
#struct Frame () ((state #u64) (words (#array #u64 1)))
#enum Outcome () ((Outcome.Empty) (Outcome.Full))
#fn choose {
  #params = ((state (#ref-mut #u64)) (full #bool));
  #returns = Outcome;
  #body = (
      (#if full
        (#block (#deref-set state 1u64) (#return (Outcome.Full)))
        (#block (#deref-set state 0u64) (#return (Outcome.Empty))))
      (#return (Outcome.Empty))
  );
}
#fn read {
  #params = ((frame Frame));
  #returns = #u64;
  #effects = (#global-access #io); #body = (
      (#loop (#match (#get frame state)
        (#case 1 (#block
          (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
          (#let answer #u64 (#deref (#get holder value)))
          (#forget holder) (#forget frame) (#return answer)))
        (#case _ (#block (#forget frame) (#return 42u64)))))
      (#return 0u64)\n  );\n}\n";

fn conditional_outcome_main(intervening: &str) -> String {
    format!(
        "{CONDITIONAL_SCALAR_OUTCOME}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut frame Frame (#struct-literal Frame
               ((state 1u64) (words (#array-repeat 0u64)))))
             (#let counter (#atomic #u64) (#atomic-init #u64 0u64))
             (#let full #bool (#u64::eq (#atomic-load (#borrow counter) #memory-relaxed) 1u64))
             (#let outcome Outcome (#call choose
               ((state (#borrow-mut (#get frame state))) (full full))))
             {intervening}
             (#let answer #u64 (#match outcome
               (#case Outcome.Empty (#call read ((frame frame))))
               (#case Outcome.Full (#block (#forget frame) 7u64))))
             (#forget counter) (#return answer)\n  );\n}}\n"
    )
}

#[test]
fn selected_empty_outcome_transfers_its_scalar_state_postcondition() {
    let source = conditional_outcome_main("");
    compile(&source)
        .expect("matching Empty proves state zero, keeping the state-one word reader inactive");
}

#[test]
fn scalar_outcome_postcondition_is_revoked_by_a_later_state_write() {
    let source = conditional_outcome_main("(#set-field frame state 1u64)");
    let error = compile(&source)
        .expect_err("a write after the call can make the missing-loan reader reachable");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}
