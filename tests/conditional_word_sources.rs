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
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn main () #u64
        (#let amount #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 0usize 1usize)
          (#struct-literal Holder (: value (#borrow amount)))))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Holder (: value (#borrow amount)))))
        (#let extracted Holder (#unsafe (#pin-read
          (#unsafe (#word-view (#pin-ref-mut Holder)
            (#borrow-slice-mut words 0usize 1usize))))))
        (#forget extracted)
        (#let neighbor Holder (#unsafe (#word-read Holder (#borrow-slice words 1usize 2usize))))
        (#let answer #u64 (#deref (#get neighbor value)))
        (#forget neighbor) (#forget words) (#return answer))";
    compile(source).expect("extracting cell zero leaves cell one's source loan intact");
}

#[test]
fn pinned_extraction_does_not_initialize_a_disjoint_word_cell() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn main () #u64
        (#let amount #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 0usize 1usize)
          (#struct-literal Holder (: value (#borrow amount)))))
        (#let extracted Holder (#unsafe (#pin-read
          (#unsafe (#word-view (#pin-ref-mut Holder)
            (#borrow-slice-mut words 0usize 1usize))))))
        (#forget extracted)
        (#let neighbor Holder (#unsafe (#word-read Holder (#borrow-slice words 1usize 2usize))))
        (#let answer #u64 (#deref (#get neighbor value)))
        (#forget neighbor) (#forget words) (#return answer))";
    let error =
        compile(&source).expect_err("extracting cell zero cannot fabricate cell one's source loan");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn cloning_a_builtin_raw_pointer_preserves_disjoint_selector_facts() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#fn main () #u64
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
        (#forget copied) (#forget words) (#return answer))";
    compile(source).expect("copying a raw pointer has no arbitrary pointee write effect");
}

#[test]
fn custom_clone_through_a_raw_pointer_invalidates_selector_facts() {
    let source = "(#struct Holder (: value (#ref #u64)))
      (#struct Payload (: target (#ptr-mut #u64)))
      (#fn Payload-clone (: value Payload) Payload
        (#unsafe (#ptr-write (#get value target) 1u64)) (#return value))
      (#fn main () #u64
        (#let-mut selector #u64 0u64)
        (#let payload Payload (#struct-literal Payload
          (: target (#ref-ptr (#borrow-mut selector)))))
        (#let copied Payload (#clone payload))
        (#let words (#array #u64 1) (#array-repeat 0u64))
        (#let answer #u64 (#match selector
          (#case 1 (#block
            (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
            (#let value #u64 (#deref (#get holder value)))
            (#forget holder) value))
          (#case _ 42u64)))
        (#forget copied) (#forget words) (#return answer))";
    let error = compile(source)
        .expect_err("an opaque user clone may mutate the selector through its pointer");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}
