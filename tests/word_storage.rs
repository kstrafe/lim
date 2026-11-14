mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

#[test]
fn stored_word_views_retain_addresses_without_granting_opaque_pointer_capabilities() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((state #u64) (words (#array #u64 1))))
      (#fn make ((source (#ref (#array #u64 1)))) Frame
        (#let-mut frame Frame (#struct-literal Frame ((state 1u64) (words (#array-repeat 0u64)))))
        (#let view (#ref #u64) (#unsafe (#word-view (#ref #u64) (#borrow-slice (#deref source)))))
        (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
          (#struct-literal Holder ((value view)))))
        (#return frame))
      (#fn read ((frame Frame)) #u64
        (#let answer #u64 (#match (#get frame state)
          (#case 1 (#block
            (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
            (#let value #u64 (#deref (#get holder value))) (#forget holder) value))
          (#case _ 0u64))) (#forget frame) (#return answer))
      (#fn main () #u64
        (#let-mut values (#array #u64 1) (#array-of 42u64))
        (#let frame Frame (#call make ((source (#borrow values)))))
        (#let answer #u64 (#call read ((frame frame)))) (#forget values) (#return answer))";
    run(source);
    let conflicting = source.replace(
        "(#let answer #u64 (#call read",
        "(#set values (#array-of 0u64)) (#let answer #u64 (#call read",
    );
    assert_eq!(
        compile(&conflicting).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let opaque = source.replace(
        "(#unsafe (#word-view (#ref #u64) (#borrow-slice (#deref source))))",
        "(#unsafe (#ptr-borrow source (#ptr-offset (#ref-ptr (#word-view (#ref #u64) (#borrow-slice (#deref source)))) 0usize)))",
    );
    let error = compile(&opaque)
        .expect_err("an opaque pointer's lifetime anchor is not a known word-cell address");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("word-storage");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn declared_frame_references_do_not_initialize_unrelated_word_cells() {
    let prefix = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((source (#ref #u64)) (words (#array #u64 1))))
      (#fn read ((frame (#ref-mut Frame))) #u64
        (#let restored Holder (#unsafe (#word-take Holder (#borrow-slice-mut (#get frame words)))))
        (#let answer #u64 (#deref (#get restored value)))
        (#forget restored) (#return answer))";
    let main = "(#fn main () #u64
      (#let owner #u64 42u64)
      (#let-mut frame Frame (#struct-literal Frame
        ((source (#borrow owner)) (words (#array-repeat 0u64)))))
      (#let answer #u64 (#call read ((frame (#borrow-mut frame)))))
      (#forget frame) (#return answer))";
    let missing = format!("{prefix}\n{main}");
    let error = compile(&missing)
        .expect_err("a declared reference is not a witness for a separate numeric cell");
    assert_eq!(error.code, DiagnosticCode::Linear);
    assert!(
        error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
    let written = main.replace(
        "(#let answer",
        "
      (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
        (#struct-literal Holder ((value (#get frame source))))))
      (#let answer",
    );
    run(&format!("{prefix}\n{written}"));
    let retired = written.replace(
        "(#let answer",
        "
      (#unsafe (#word-forget Holder (#borrow-slice-mut (#get frame words))))
      (#let answer",
    );
    let error = compile(&format!("{prefix}\n{retired}"))
        .expect_err("the surviving source field cannot revive a retired word-cell loan");
    assert_eq!(error.code, DiagnosticCode::Linear);
}

#[test]
fn loop_dispatch_proves_initialization_in_every_reachable_read_context() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn work ((flag #bool)) #u64
        (#let amount #u64 42u64)
        (#let-mut result #u64 0u64)
        (#let-mut state #u64 0u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#loop (#match state
          (#case 0 (#block
            (#unsafe (#word-write Holder (#borrow-slice-mut words)
              (#struct-literal Holder ((value (#borrow amount))))))
            (#set state 1u64) (#continue) (#unreachable)))
          (#case 1 (#block
            (#let restored Holder (#unsafe (#word-take Holder (#borrow-slice-mut words))))
            (#let answer #u64 (#deref (#get restored value)))
            (#forget restored) (#set result answer)
            (#set state 2u64) (#continue) (#unreachable)))
          (#case 2 (#block (#forget words) (#return result) (#unreachable)))
          (#case _ (#unreachable))))
        (#forget words) (#return 0u64))
      (#fn main () #u64 (#return (#call work ((flag true)))))";
    run(source);
    let write = "(#unsafe (#word-write Holder (#borrow-slice-mut words)
              (#struct-literal Holder ((value (#borrow amount))))))";
    for replacement in [
        String::new(),
        format!("(#if flag (#block {write}) ())"),
        format!("{write} (#unsafe (#word-forget Holder (#borrow-slice-mut words)))"),
    ] {
        let invalid = source.replace(write, &replacement);
        assert_ne!(invalid, source);
        let error = compile(&invalid).expect_err("every reachable read needs real initialization");
        assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    }
}

#[test]
fn scalar_dispatch_does_not_require_loans_from_proven_unreachable_readers() {
    let source = "
      (#struct Holder () ((value (#ref #u64))))
      (#fn number () #u64 (#return 1u64))
      (#fn main () #u64
        (#let-mut selector #u64 1u64)
        (#let words (#array #u64 1) (#array-repeat 0u64))
        (#let result #u64 (#match selector
          (#case 0 (#block
            (#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words))))
            (#let amount #u64 (#deref (#get restored value)))
            (#forget restored) amount))
          (#case 1 42u64) (#case _ 0u64)))
        (#forget words) (#return result))";
    run(source);
    let called_selector = source.replace("#u64 1u64)", "#u64 (#call number ()))");
    run(&called_selector);
    for invalid in [
        source.replace("#u64 1u64)", "#u64 0u64)"),
        called_selector.replace("(#return 1u64)", "(#return 0u64)"),
        source.replace(
            "(#let result #u64",
            "(#deref-set (#borrow-mut selector) 0u64) (#let result #u64",
        ),
    ] {
        let error =
            compile(&invalid).expect_err("an unknown or selected reader needs actual provenance");
        assert_eq!(error.code, DiagnosticCode::Linear);
    }
}

#[test]
fn scalar_loop_field_bounds_exclude_only_proven_unreachable_word_readers() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct State () ((pc #u64)))
      (#fn dispatch ((condition #bool)) #u64
        (#let-mut state State (#struct-literal State ((pc 0u64))))
        (#let words (#array #u64 1) (#array-repeat 0u64))
        (#while condition (#set state (#struct-literal State ((pc 1u64)))))
        (#let answer #u64 (#match (#get state pc)
          (#case 2 (#block
            (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
            (#let amount #u64 (#deref (#get holder value)))
            (#forget holder) amount))
          (#case _ 42u64)))
        (#forget words) (#return answer))
      (#fn main () #u64 (#return (#call dispatch ((condition false)))))";
    run(source);
    let selected = source.replace("((pc 1u64))", "((pc 2u64))");
    let error =
        compile(&selected).expect_err("a reachable reader still needs its exact stored loan");
    assert_eq!(error.code, DiagnosticCode::Linear);
}

#[test]
fn clone_hook_writes_cannot_leave_stale_scalar_reader_bounds() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Payload () ((target (#ptr-mut #u64))))
      (#fn Payload::clone ((value Payload)) Payload
        (#unsafe (#ptr-write (#get value target) 1u64)) (#return value))
      (#fn main () #u64
        (#let-mut selector #u64 0u64)
        (#let payload Payload (#struct-literal Payload
          ((target (#ref-ptr (#borrow-mut selector))))))
        (#let cloned Payload (#clone payload))
        (#let words (#array #u64 1) (#array-repeat 0u64))
        (#let answer #u64 (#match selector
          (#case 1 (#block
            (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
            (#let amount #u64 (#deref (#get holder value)))
            (#forget holder) amount))
          (#case _ 42u64)))
        (#forget words) (#return answer))";
    let error =
        compile(source).expect_err("a custom clone can mutate a selector through its raw pointer");
    assert_eq!(error.code, DiagnosticCode::Linear);
    assert!(
        error.message.contains("loan")
            || error.message.contains("unresolved")
            || error.message.contains("missing slot provenance"),
        "{error:?}"
    );
    let valid = source.replace(
        "(#case 1 (#block
            (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice words))))
            (#let amount #u64 (#deref (#get holder value)))
            (#forget holder) amount))
          (#case _ 42u64)",
        "(#case 1 42u64) (#case _ 0u64)",
    );
    run(&valid);
}

#[test]
fn selected_parameter_cases_exclude_only_fresh_nested_word_readers() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((selector #u64) (words (#array #u64 1))))
      (#fn read ((frame (#ref-mut Frame))) #u64
        (#return (#match (#get frame selector)
          (#case 1 (#block
            (#let answer #u64 (#match (#get frame selector)
              (#case 0 (#block
                (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
                (#let value #u64 (#deref (#get holder value)))
                (#forget holder) value))
              (#case _ 42u64))) answer))
          (#case _ 0u64))))
      (#fn main () #u64
        (#let-mut frame Frame (#struct-literal Frame
          ((selector 1u64) (words (#array-repeat 0u64)))))
        (#let answer #u64 (#call read ((frame (#borrow-mut frame)))))
        (#forget frame) (#return answer))";
    run(source);
    for reachable in [
        source.replace("(#case 0 (#block", "(#case 1 (#block"),
        source.replace(
            "(#let answer #u64 (#match",
            "(#deref-set (#borrow-mut (#get frame selector)) 0u64)
            (#let answer #u64 (#match",
        ),
    ] {
        let error = compile(&reachable).expect_err(
            "the nested reader needs a loan if selected or reached after a selector write",
        );
        assert_eq!(error.code, DiagnosticCode::Linear);
    }
}

#[test]
fn conditional_owned_word_returns_require_every_path_to_initialize_the_cell() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Storage () ((words (#array #u64 1))))
      (#fn make ((value (#ref #u64)) (flag #bool)) Storage
        (#let-mut storage Storage (#struct-literal Storage ((words (#array-repeat 0u64)))))
        (#if flag (#unsafe (#word-write Holder (#borrow-slice-mut (#get storage words))
          (#struct-literal Holder ((value value))))) ())
        (#return storage))
      (#fn read ((storage Storage)) #u64
        (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get storage words)))))
        (#let answer #u64 (#deref (#get holder value)))
        (#forget holder) (#forget storage) (#return answer))
      (#fn main () #u64
        (#let value #u64 42u64)
        (#return (#call read ((storage (#call make ((value (#borrow value)) (flag false))))))))";
    assert_eq!(
        compile(source)
            .expect_err("a conditional owned-return loan is not initialized on every return path")
            .code,
        DiagnosticCode::Linear
    );
    let write = "(#unsafe (#word-write Holder (#borrow-slice-mut (#get storage words))
          (#struct-literal Holder ((value value)))))";
    // An unconditional write and two alternatives that both initialize the
    // slot remain valid; this is not a blanket ban on returned word storage.
    let definite = source.replace(&format!("(#if flag {write} ())"), write);
    assert_ne!(definite, source);
    run(&definite);
    run(&source.replace(
        &format!("(#if flag {write} ())"),
        &format!("(#if flag {write} {write})"),
    ));
    let direct = source.replace(
        "(#return (#call read ((storage (#call make ((value (#borrow value)) (flag false)))))))",
        "(#let storage Storage (#call make ((value (#borrow value)) (flag false))))
        (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get storage words)))))
        (#let answer #u64 (#deref (#get holder value)))
        (#forget holder) (#forget storage) (#return answer)",
    );
    assert_ne!(direct, source);
    assert_eq!(
        compile(&direct)
            .expect_err("a direct load must also require every-path initialization")
            .code,
        DiagnosticCode::Linear
    );
    run(&direct.replace(&format!("(#if flag {write} ())"), write));
    let lifetime = source.replace("(#let value #u64 42u64)", "(#let-mut value #u64 42u64)")
        .replace("(#return (#call read ((storage (#call make ((value (#borrow value)) (flag false)))))))",
            "(#let storage Storage (#call make ((value (#borrow value)) (flag false))))
            (#set value 0u64) (#forget storage) (#return value)");
    assert_eq!(
        compile(&lifetime)
            .expect_err("possible retained loans must still protect their pointee")
            .code,
        DiagnosticCode::Borrow
    );
    let initialized = "(#call initialized ((value value) (flag flag)))";
    let empty = "(#struct-literal Storage ((words (#array-repeat 0u64))))";
    let initialized_definition = definite
        .split("      (#fn read")
        .next()
        .unwrap()
        .replace("(#fn make", "(#fn initialized");
    let remaining = source.split("      (#fn read").nth(1).unwrap();
    for result in [
        format!("(#if flag {initialized} {empty})"),
        format!("(#match (#if flag 1u64 0u64) (#case 1 {initialized}) (#case _ {empty}))"),
        format!("(#loop (#if flag (#block (#break {initialized})) (#block (#break {empty}))))"),
    ] {
        let alternative = format!(
            "{initialized_definition}
          (#fn make ((value (#ref #u64)) (flag #bool)) Storage (#return {result}))
          (#fn read{remaining}"
        );
        let error = compile(&alternative)
            .expect_err("every reachable value alternative must initialize the slot");
        assert_eq!(error.code, DiagnosticCode::Linear, "{result}: {error:?}");
        let initialized_result = result.replace(empty, initialized);
        run(&format!(
            "{initialized_definition}
          (#fn make ((value (#ref #u64)) (flag #bool)) Storage (#return {initialized_result}))
          (#fn read{remaining}"
        ));
    }
}

#[test]
fn conditional_call_effects_cannot_initialize_or_revive_word_loans() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((source (#ref #u64)) (words (#array #u64 1)) (other (#array #u64 1))))
      (#fn conditional ((frame (#ref-mut Frame)) (flag #bool)) ()
        (#if flag
          (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame other))
            (#struct-literal Holder ((value (#get frame source)))))) ())
        (#return ()))
      (#fn work ((frame (#ref-mut Frame)) (flag #bool)) #u64
        (#loop
          (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
            (#struct-literal Holder ((value (#get frame source))))))
          (#call conditional ((frame frame) (flag flag)))
          (#let restored Holder (#unsafe (#word-take Holder (#borrow-slice-mut (#get frame words)))))
          (#let answer #u64 (#deref (#get restored value)))
          (#forget restored) (#return answer))
        (#return 0u64))
      (#fn main () #u64
        (#let value #u64 42u64)
        (#let-mut frame Frame (#struct-literal Frame
          ((source (#borrow value)) (words (#array-repeat 0u64)) (other (#array-repeat 0u64)))))
        (#let answer #u64 (#call work ((frame (#borrow-mut frame)) (flag true))))
        (#forget frame) (#return answer))";
    run(source);
    run(&source.replace("(flag true)", "(flag false)"));
    let retirement = source.replace(
        "(#word-write Holder (#borrow-slice-mut (#get frame other))\n            (#struct-literal Holder ((value (#get frame source)))))",
        "(#word-forget Holder (#borrow-slice-mut (#get frame words)))",
    );
    assert_ne!(retirement, source);
    assert_eq!(
        compile(&retirement)
            .expect_err("a possible retirement cannot retain an old may-origin as permission")
            .code,
        DiagnosticCode::Linear
    );
    let initialization = source.replace("(#get frame other)", "(#get frame words)")
        .replace("(#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))\n            (#struct-literal Holder ((value (#get frame source))))))\n          (#call conditional",
            "(#call conditional");
    assert_ne!(initialization, source);
    assert_eq!(
        compile(&initialization.replace("(flag true)", "(flag false)"))
            .expect_err("a possible write is not definite initialization of a reader")
            .code,
        DiagnosticCode::Linear
    );
    let overwritten = retirement.replace(
        "(#let restored Holder",
        "(#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
          (#struct-literal Holder ((value (#get frame source))))))
        (#let restored Holder",
    );
    run(&overwritten);
}

#[test]
fn returned_state_guarantees_initialize_only_the_corresponding_owned_cells() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((state #u64) (words (#array #u64 1))))
      (#fn make ((value (#ref #u64)) (flag #bool)) Frame
        (#let-mut frame Frame (#struct-literal Frame ((state 0u64) (words (#array-repeat 0u64)))))
        (#if flag (#block
          (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
            (#struct-literal Holder ((value value)))))
          (#set-field frame state 1u64)) ())
        (#return frame))
      (#fn read ((frame Frame)) #u64
        (#loop (#match (#get frame state)
          (#case 1 (#block
            (#let holder Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
            (#let answer #u64 (#deref (#get holder value)))
            (#forget holder) (#forget frame) (#return answer)))
          (#case _ (#block (#forget frame) (#return 42u64)))))
        (#return 0u64))
      (#fn main () #u64
        (#let value #u64 42u64)
        (#let-mut frame Frame (#call make ((value (#borrow value)) (flag false))))
        (#return (#call read ((frame frame)))))";
    run(source);
    run(&source.replace("(flag false)", "(flag true)"));
    for invalid in [
        source.replace("(#return (#call read", "(#set-field frame state 1u64) (#return (#call read"),
        source.replace("(#return (#call read", "(#unsafe (#word-forget Holder (#borrow-slice-mut (#get frame words)))) (#return (#call read"),
        source.replace("1u64)) ())", "1u64)) (#block (#set-field frame state 1u64)))"),
    ] {
        assert_ne!(invalid, source);
        let error = compile(&invalid).expect_err("changed or unproved state cannot initialize a word cell");
        assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    }
}

#[test]
fn persistent_cells_and_transient_copies_have_distinct_entry_obligations() {
    let source = "(#struct Stored () ((view (#ref #u64))))
      (#struct Frame () ((pc #u64) (source (#ref #u64)) (kept (#array #u64 1)) (temporary (#array #u64 1))))
      (#enum Poll () ((Poll.Pending Frame) (Poll.Ready #u64)))
      (#fn read ((value Stored)) #u64 (#return (#deref (#get value view))))
      (#fn step ((input Frame)) Poll
        (#let-mut frame Frame input)
        (#loop (#match (#get frame pc)
          (#case 0 (#block
            (#let view (#ref #u64) (#get frame source))
            (#unsafe (#word-write Stored (#borrow-slice-mut (#get frame kept))
              (#struct-literal Stored ((view view)))))
            (#set-field frame pc 1u64)
            (#return (Poll.Pending (#unsafe (#pin-read (#pin-borrow-mut frame))))) (#unreachable)))
          (#case 1 (#block
            (#let restored Stored (#unsafe (#word-read Stored (#borrow-slice (#get frame kept)))))
            (#unsafe (#word-write Stored (#borrow-slice-mut (#get frame temporary)) restored))
            (#let answer #u64 (#call read ((value (#unsafe (#word-read Stored (#borrow-slice (#get frame temporary))))))))
            (#forget frame) (#return (Poll.Ready answer)) (#unreachable)))
          (#case _ (#unreachable)))) (#forget frame) (#return (#unreachable)))
      (#fn main () #u64
        (#let-mut value #u64 42u64)
        (#let frame Frame (#struct-literal Frame
          ((pc 0u64) (source (#borrow value)) (kept (#array-repeat 0u64)) (temporary (#array-repeat 0u64)))))
        (#let first Poll (#call step ((input frame))))
        (#let-else (Poll.Pending resumed) Poll first (#unreachable))
        (#return (#match (#call step ((input resumed)))
          (#case (Poll.Ready answer) answer) (#case (Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable))))))";
    run(source);
    let missing = source.replace("(pc 0u64)", "(pc 1u64)");
    assert_eq!(compile(&missing).unwrap_err().code, DiagnosticCode::Linear);
    let invalidated = source.replace(
        "(#return (#match (#call step",
        "(#set value 0u64) (#return (#match (#call step",
    );
    assert_eq!(
        compile(&invalidated).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let retired = source.replace("(Poll.Pending resumed)", "(Poll.Pending saved)")
        .replace("(#return (#match (#call step", "(#let-mut resumed Frame saved) (#unsafe (#word-forget Stored (#borrow-slice-mut (#get resumed kept)))) (#return (#match (#call step");
    assert_eq!(compile(&retired).unwrap_err().code, DiagnosticCode::Linear);
}

#[test]
fn a_loop_backedge_store_does_not_initialize_a_direct_resume_entry() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((pc #u64) (source (#ref #u64)) (words (#array #u64 1))))
      (#fn work ((frame (#ref-mut Frame))) #u64
        (#loop (#match (#get frame pc)
          (#case 0 (#block
            (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
              (#struct-literal Holder ((value (#get frame source))))))
            (#deref-set (#borrow-mut (#get frame pc)) 1u64) (#continue) (#unreachable)))
          (#case 1 (#block
            (#let holder Holder (#unsafe (#word-take Holder (#borrow-slice-mut (#get frame words)))))
            (#let answer #u64 (#deref (#get holder value)))
            (#forget holder) (#return answer) (#unreachable)))
          (#case _ (#block (#return 0u64) (#unreachable))))) (#return 0u64))
      (#fn main () #u64
        (#let value #u64 42u64)
        (#let-mut frame Frame (#struct-literal Frame
          ((pc 1u64) (source (#borrow value)) (words (#array-repeat 0u64)))))
        (#let answer #u64 (#call work ((frame (#borrow-mut frame)))))
        (#forget frame) (#return answer))";
    let error =
        compile(source).expect_err("a store on a different loop path is not an entry loan witness");
    assert_eq!(error.code, DiagnosticCode::Linear);
    let initial_entry = source.replace("(pc 1u64)", "(pc 0u64)");
    run(&initial_entry);
    let (owned_prefix, owned_main) = initial_entry.split_once("(#fn main").unwrap();
    let owned_prefix = owned_prefix
        .replace(
            "((frame (#ref-mut Frame))) #u64",
            "((frame Frame)) #u64 (#let-mut state Frame frame)",
        )
        .replace("(#get frame", "(#get state")
        .replace("(#return answer)", "(#forget state) (#return answer)")
        .replace("(#return 0u64)", "(#forget state) (#return 0u64)");
    let owned_main = owned_main
        .replace("((frame (#borrow-mut frame)))", "((frame frame))")
        .replace("(#forget frame)", "");
    let owned_entry = format!("{owned_prefix}(#fn main{owned_main}");
    run(&owned_entry);
    assert_eq!(
        compile(&owned_entry.replace("(pc 0u64)", "(pc 1u64)"))
            .expect_err("owned resume entries require the same real backing loans")
            .code,
        DiagnosticCode::Linear
    );
    let projected_wrapper = "(#struct Pair () ((inner Frame) (decoy Frame)))
      (#struct Nest () ((selected Pair) (decoy Pair)))
      (#fn from-pair ((root Pair)) #u64
        (#let answer #u64 (#call work ((frame (#get root inner)))))
        (#forget root) (#return answer))
      (#fn from-nest ((root Nest)) #u64
        (#let answer #u64 (#call from-pair ((root (#get root selected)))))
        (#forget root) (#return answer))";
    let selected = "(#struct-literal Frame
      ((pc 0u64) (source (#borrow value)) (words (#array-repeat 0u64))))";
    let resumed = selected.replace("(pc 0u64)", "(pc 1u64)");
    let pair = format!("(#struct-literal Pair ((inner {selected}) (decoy {resumed})))");
    let opposite = format!("(#struct-literal Pair ((inner {resumed}) (decoy {selected})))");
    let nested_main = format!(
        "(#fn main () #u64
      (#let value #u64 42u64)
      (#return (#call from-nest ((root (#struct-literal Nest
        ((selected {pair}) (decoy {opposite}))))))))"
    );
    run(&format!("{owned_prefix}{projected_wrapper}{nested_main}"));
    let bad_nested_main = nested_main.replace(
        &format!("(selected {pair}) (decoy {opposite})"),
        &format!("(selected {opposite}) (decoy {pair})"),
    );
    assert_ne!(bad_nested_main, nested_main);
    assert_eq!(
        compile(&format!(
            "{owned_prefix}{projected_wrapper}{bad_nested_main}"
        ))
        .expect_err("a nested decoy selector cannot waive the selected frame's obligation")
        .code,
        DiagnosticCode::Linear
    );
    let constructor = "(#fn make-frame ((source (#ref #u64))) Frame
      (#return (#struct-literal Frame
        ((pc 0u64) (source source) (words (#array-repeat 0u64))))))";
    let constructed = initial_entry.replace(
        "(#struct-literal Frame\n          ((pc 0u64) (source (#borrow value)) (words (#array-repeat 0u64))))",
        "(#call make-frame ((source (#borrow value))))",
    );
    assert_ne!(constructed, initial_entry);
    run(&format!("{constructor}\n{constructed}"));
    let resumed_constructor = constructor.replace("(pc 0u64)", "(pc 1u64)");
    assert_eq!(
        compile(&format!("{resumed_constructor}\n{constructed}"))
            .expect_err("returned numeric facts must reflect the actual constructor")
            .code,
        DiagnosticCode::Linear
    );
    let forwarded_constructor = "(#fn make-forward ((source (#ref #u64))) Frame
      (#return (#call make-frame ((source source)))))";
    run(&format!(
        "{constructor}\n{forwarded_constructor}\n{}",
        constructed.replace("(#call make-frame", "(#call make-forward")
    ));
    let clone_hook = "(#fn Frame::clone ((source Frame)) Frame
      (#let owner (#ref #u64) (#get source source)) (#forget source)
      (#return (#struct-literal Frame
        ((pc 1u64) (source owner) (words (#array-repeat 0u64))))))";
    let cloned_entry = initial_entry
        .replace(
            "(#let answer #u64 (#call work",
            "(#let-mut clone Frame (#clone frame))
        (#let answer #u64 (#call work",
        )
        .replace(
            "((frame (#borrow-mut frame)))))",
            "((frame (#borrow-mut clone)))))",
        )
        .replace(
            "(#forget frame) (#return answer)",
            "(#forget clone) (#forget frame) (#return answer)",
        );
    assert_eq!(
        compile(&format!("{clone_hook}\n{cloned_entry}"))
            .expect_err("a clone hook result does not retain the source's numeric selector")
            .code,
        DiagnosticCode::Linear
    );
    let changed_entry = initial_entry.replace(
        "(#let answer #u64 (#call work",
        "(#deref-set (#borrow-mut (#get frame pc)) 1u64)
        (#let answer #u64 (#call work",
    );
    assert_eq!(
        compile(&changed_entry)
            .expect_err(
                "the actual entry value, not the original constructor, selects the contract"
            )
            .code,
        DiagnosticCode::Linear
    );
    let unknown_entry = source.replace("(pc 1u64)", "(pc (#call number ()))");
    assert_eq!(
        compile(&format!(
            "(#fn number () #u64 (#return 1u64))\n{unknown_entry}"
        ))
        .expect_err("unknown entry values retain the required backing loans")
        .code,
        DiagnosticCode::Linear
    );
    let initialized = source.replace(
        "(#let answer #u64 (#call work",
        "(#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
          (#struct-literal Holder ((value (#get frame source))))))
        (#let answer #u64 (#call work",
    );
    run(&initialized);
    let retired = initialized.replace(
        "(#let answer #u64 (#call work",
        "(#unsafe (#word-forget Holder (#borrow-slice-mut (#get frame words))))
        (#let answer #u64 (#call work",
    );
    assert_eq!(
        compile(&retired)
            .expect_err("retired backing cells cannot satisfy a resume entry")
            .code,
        DiagnosticCode::Linear
    );
    let wrapper = "(#fn forward ((frame (#ref-mut Frame))) #u64
      (#return (#call work ((frame frame)))))";
    let forwarded = source.replace(
        "(#call work ((frame (#borrow-mut frame))))",
        "(#call forward ((frame (#borrow-mut frame))))",
    );
    assert_eq!(
        compile(&format!("{wrapper}\n{forwarded}"))
            .expect_err("forwarding must preserve the missing entry obligation")
            .code,
        DiagnosticCode::Linear
    );
    let forwarded_initialized = initialized.replace(
        "(#call work ((frame (#borrow-mut frame))))",
        "(#call forward ((frame (#borrow-mut frame))))",
    );
    run(&format!("{wrapper}\n{forwarded_initialized}"));
    run(&format!(
        "{wrapper}\n{}",
        initial_entry.replace(
            "(#call work ((frame (#borrow-mut frame))))",
            "(#call forward ((frame (#borrow-mut frame))))",
        )
    ));
    let changed_wrapper = wrapper.replace(
        "(#return",
        "(#deref-set (#borrow-mut (#get frame pc)) 1u64) (#return",
    );
    let forwarded_initial = initial_entry.replace(
        "(#call work ((frame (#borrow-mut frame))))",
        "(#call forward ((frame (#borrow-mut frame))))",
    );
    assert_eq!(
        compile(&format!("{changed_wrapper}\n{forwarded_initial}"))
            .expect_err("forwarding after a selector write cannot retain an entry guard")
            .code,
        DiagnosticCode::Linear
    );

    let wildcard_reader = source.replace(
        "(#case _ (#block (#return 0u64) (#unreachable)))",
        "(#case _ (#block
          (#let fallback-holder Holder (#unsafe (#word-take Holder (#borrow-slice-mut (#get frame words)))))
          (#let fallback-answer #u64 (#deref (#get fallback-holder value)))
          (#forget fallback-holder) (#return fallback-answer) (#unreachable)))",
    ).replace("(pc 1u64)", "(pc 2u64)");
    assert_eq!(
        compile(&wildcard_reader)
            .expect_err("the residual partition must retain wildcard reader requirements")
            .code,
        DiagnosticCode::Linear
    );
}

fn run(source: &str) {
    let assembly = compile(source).unwrap();
    let scratch = support::Scratch::new("word-storage-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        &mut std::process::Command::new(binary),
        std::time::Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

const SOURCE: &str = "
(#struct Pair () ((left #u8) (right #u64)))
(#fn inspect ((pair (#ref Pair))) #u64
  (#return (#u64::add-wrap (#as (#get pair left) #u64) (#get pair right))))
(#fn main () #u64
  (#let-mut words (#array #u64 2) (#array-repeat 0u64))
  (#unsafe (#word-write Pair (#borrow-slice-mut words)
    (#struct-literal Pair ((left 40u8) (right 2u64)))))
  (#let view (#ref Pair) (#unsafe (#word-view (#ref Pair) (#borrow-slice words))))
  (#let result #u64 (#call inspect ((pair view))))
  (#forget view) (#return result))";

#[test]
fn flat_word_views_preserve_stack_layout() {
    run(SOURCE);
}

const EMPTY_REFERENCE_CELL: &str = "
(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
(#fn main () #u64
  (#let-mut words (#array #u64 2) (#array-repeat 0u64))
  (#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))
  (#let cell Cell (#unsafe (#word-take Cell (#borrow-slice-mut words))))
  (#forget cell) (#return 42u64))";

const OPTIONAL_WORD_READER: &str = "
(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
(#fn inspect ((words (#slice #u64))) #u64
  (#let cell Cell (#unsafe (#word-read Cell words)))
  (#return (#match cell
    (#case (Cell.Vacant) 42u64)
    (#case (Cell.Occupied value) (#deref value)))))
(#fn main () #u64
  (#let amount #u64 42u64)
  (#let-mut words (#array #u64 2) (#array-repeat 0u64))
  (#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))
  (#let answer #u64 (#call inspect ((words (#borrow-slice words)))))
  (#forget words) (#return answer))";

#[test]
fn typed_view_cleanup_publishes_empty_tags_and_retires_actual_word_loans() {
    let source = "(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
      (#fn clear ((slot (#pin-ref-mut Cell))) ()
        (#unsafe (#forget (#pin-read slot)))
        (#unsafe (#pin-write slot (Cell.Vacant))) (#return ()))
      (#fn main () #u64
        (#let-mut amount #u64 40u64)
        (#let-mut words (#array #u64 4) (#array-repeat 0u64))
        (#unsafe (#word-write Cell (#borrow-slice-mut words 1usize 3usize) (Cell.Occupied (#borrow amount))))
        (#call clear ((slot (#unsafe (#word-view (#pin-ref-mut Cell) (#borrow-slice-mut words 1usize 3usize))))))
        (#set amount 42u64)
        (#let value Cell (#unsafe (#word-read Cell (#borrow-slice words 1usize 3usize))))
        (#forget value) (#forget words) (#return amount))";
    run(source);
}

#[test]
fn typed_view_writers_export_real_loans_at_nested_physical_offsets() {
    let source = "(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
      (#struct Buffer () ((prefix #u64) (cell Cell) (suffix #u64)))
      (#fn install ((buffer (#pin-ref-mut Buffer)) (value (#ref #u64))) ()
        (#unsafe (#forget (#pin-read (#pin-borrow-mut (#get buffer cell)))))
        (#unsafe (#pin-write (#pin-borrow-mut (#get buffer cell)) (Cell.Occupied value))) (#return ()))
      (#fn clear ((buffer (#pin-ref-mut Buffer))) ()
        (#unsafe (#forget (#pin-read (#pin-borrow-mut (#get buffer cell)))))
        (#unsafe (#pin-write (#pin-borrow-mut (#get buffer cell)) (Cell.Vacant))) (#return ()))
      (#fn main () #u64
        (#let-mut amount #u64 42u64)
        (#let-mut words (#array #u64 6) (#array-repeat 0u64))
        (#unsafe (#word-write Buffer (#borrow-slice-mut words 1usize 5usize)
          (#struct-literal Buffer ((prefix 40u64) (cell (Cell.Vacant)) (suffix 2u64)))))
        (#call install ((buffer (#unsafe (#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 5usize)))) (value (#borrow amount))))
        (#let cell Cell (#unsafe (#word-read Cell (#borrow-slice words 2usize 4usize))))
        (#let answer #u64 (#match cell (#case (Cell.Vacant) 0u64) (#case (Cell.Occupied view) (#deref view))))
        (#call clear ((buffer (#unsafe (#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 5usize))))))
        (#set amount 0u64)
        (#assert (#u64::eq (#unsafe (#word-read #u64 (#borrow-slice words 1usize 2usize))) 40u64))
        (#assert (#u64::eq (#unsafe (#word-read #u64 (#borrow-slice words 4usize 5usize))) 2u64))
        (#forget words) (#return answer))";
    run(source);
    let invalid = source.replace("(#let cell Cell", "(#set amount 0u64) (#let cell Cell");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
    let escaped = source.replace("(#let answer #u64", "(#let escaped (#ref #u64) (#match (#unsafe (#word-read Cell (#borrow-slice words 2usize 4usize))) (#case (Cell.Vacant) (#borrow amount)) (#case (Cell.Occupied view) view))) (#let answer #u64")
        .replace("(#forget words) (#return answer)", "(#forget escaped) (#forget words) (#return answer)");
    assert_eq!(compile(&escaped).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn typed_view_mutation_footprints_preserve_neighboring_empty_cells() {
    let source = "(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
      (#fn clear ((slot (#pin-ref-mut Cell))) ()
        (#unsafe (#forget (#pin-read slot)))
        (#unsafe (#pin-write slot (Cell.Vacant))) (#return ()))
      (#fn main () #u64
        (#let amount #u64 42u64)
        (#let-mut words (#array #u64 4) (#array-repeat 0u64))
        (#unsafe (#word-write Cell (#borrow-slice-mut words 0usize 2usize) (Cell.Occupied (#borrow amount))))
        (#unsafe (#word-write Cell (#borrow-slice-mut words 2usize 4usize) (Cell.Vacant)))
        (#call clear ((slot (#unsafe (#word-view (#pin-ref-mut Cell) (#borrow-slice-mut words))))))
        (#let neighbor Cell (#unsafe (#word-read Cell (#borrow-slice words 2usize 4usize))))
        (#forget neighbor) (#forget words) (#return 42u64))";
    run(source);
}

#[test]
fn typed_view_writes_through_stored_references_do_not_overwrite_pointer_words() {
    let source = "(#struct External () ((amount #u64)))
      (#struct Holder () ((target (#ref-mut External))))
      (#fn change ((holder (#ref-mut Holder))) ()
        (#deref-set (#borrow-mut (#get (#get holder target) amount)) 42u64) (#return ()))
      (#fn main () #u64
        (#let-mut external External (#struct-literal External ((amount 40u64))))
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words) (#struct-literal Holder ((target (#borrow-mut external))))))
        (#call change ((holder (#unsafe (#word-view (#ref-mut Holder) (#borrow-slice-mut words))))))
        (#let holder Holder (#unsafe (#word-take Holder (#borrow-slice-mut words))))
        (#let target (#ref-mut External) (#get holder target))
        (#forget holder) (#forget words)
        (#let answer #u64 (#get target amount)) (#forget target) (#forget external)
        (#return answer))";
    run(source);
}

#[test]
fn metadata_only_helpers_preserve_tags_but_never_restore_retired_loans() {
    let source = OPTIONAL_WORD_READER
        .replace(
            "(#fn main",
            "(#fn retire ((words (#slice-mut #u64))) ()
           (#unsafe (#word-forget Cell words)) (#return ()))
         (#fn forward-retire ((words (#slice-mut #u64))) ()
           (#call retire ((words words))) (#return ()))
         (#fn main",
        )
        .replace(
            "(#let answer",
            "(#call forward-retire ((words (#borrow-slice-mut words)))) (#let answer",
        );
    run(&source);
    for invalid in [
        source.replace("(Cell.Vacant)))\n  (#call", "(Cell.Occupied (#borrow amount))))\n  (#call"),
        source.replace("(#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))", ""),
        source.replace("(#call forward-retire", "(#unsafe (#word-write #u64 (#borrow-slice-mut words 0usize 1usize) 0u64)) (#call forward-retire"),
    ] {
        assert_ne!(invalid, source);
        let error = compile(&invalid).unwrap_err();
        assert!(error.message.contains("missing required input loan") || error.message.contains("unresolved call inputs"), "{error:?}");
    }
}

#[test]
fn word_owner_restoration_preserves_borrowed_pointee_fields() {
    let source = "(#struct Holder () ((link (#ref #u64))))
      (#struct Words () ((words (#array #u64 1))))
      (#fn restore ((storage (#ref-mut Words))) (#pin-own Holder)
        (#return (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get storage words))))))
      (#fn forward ((storage (#ref-mut Words))) (#pin-own Holder)
        (#return (#call restore ((storage storage)))))
      (#fn main () #u64
        (#let-mut amount #u64 42u64)
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let-mut storage Words (#struct-literal Words ((words (#array-repeat 0u64)))))
        (#unsafe (#word-write (#pin-own Holder) (#borrow-slice-mut (#get storage words))
          (#pin-own-of pointer (#struct-literal Holder ((link (#borrow amount)))))))
        (#let owner (#pin-own Holder) (#call forward ((storage (#borrow-mut storage)))))
        (#let view (#pin-ref Holder) (#pin-own-borrow (#borrow owner)))
        (#let answer #u64 (#deref (#get view link))) (#forget view)
        (#let retired (#ptr-mut Holder) (#unsafe (#pin-release owner)))
        (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (retired 4096usize))) 0i64))
        (#forget storage) (#return answer))";
    run(source);
    let owned = source.replace(
        "(#fn restore ((storage (#ref-mut Words))) (#pin-own Holder)\n        (#return (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get storage words))))))",
        "(#fn restore ((storage Words)) (#pin-own Holder)
          (#let-mut working Words storage)
          (#let restored (#pin-own Holder) (#unsafe (#word-take (#pin-own Holder) (#borrow-slice-mut (#get working words)))))
          (#forget working) (#return restored))",
    ).replace("(#struct Words () ((words (#array #u64 1))))", "(#struct Words (#linear) ((words (#array #u64 1)))) ")
        .replace("(#fn forward ((storage (#ref-mut Words)))", "(#fn forward ((storage Words))")
        .replace("(#call forward ((storage (#borrow-mut storage))))", "(#call forward ((storage storage)))")
        .replace("(#forget storage)", "");
    assert!(owned.contains("(#let-mut working Words storage)"));
    run(&owned);
    let invalid_owned = owned.replace("(#let answer", "(#set amount 0u64) (#let answer");
    assert_eq!(
        compile(&invalid_owned).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    for invalid in [
        source.replace("(#let answer", "(#set amount 0u64) (#let answer"),
        source.replace("(#forget view)", ""),
        source.replace("(#let owner", "(#unsafe (#word-forget (#pin-own Holder) (#borrow-slice-mut (#get storage words)))) (#let owner"),
        source.replace("(#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder)", "(#let pointer (#ptr-mut #u64) (#unsafe (#linux-syscall (#ptr-mut #u64)")
            .replace("(#word-write (#pin-own Holder)", "(#word-write (#pin-own #u64)")
            .replace("(#struct-literal Holder ((link (#borrow amount))))", "42u64"),
    ] {
        let error = compile(&invalid).unwrap_err();
        assert!(error.code == DiagnosticCode::Borrow || error.message.contains("missing slot provenance")
            || error.message.contains("missing required input loan"), "{error:?}");
    }
}

#[test]
fn optional_owned_word_results_require_their_allocation_pointer() {
    let source = "(#enum Input () ((Input.NoInput) (Input.HasInput (#pin-own #u64))))
      (#enum Output () ((Output.NoOutput) (Output.HasOutput (#pin-own #u64))))
      (#struct Words () ((words (#array #u64 2))))
      (#fn convert ((storage (#ref-mut Words))) Output
        (#let input Input (#unsafe (#word-take Input (#borrow-slice-mut (#get storage words)))))
        (#return (#match input (#case (Input.NoInput) (Output.NoOutput)) (#case (Input.HasInput owner) (Output.HasOutput owner)))))
      (#fn forward ((storage (#ref-mut Words))) Output
        (#return (#call convert ((storage storage)))))
      (#fn main () #u64
        (#let pointer (#ptr-mut #u64) (#unsafe (#linux-syscall (#ptr-mut #u64) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let-mut storage Words (#struct-literal Words ((words (#array-repeat 0u64)))))
        (#unsafe (#word-write Input (#borrow-slice-mut (#get storage words)) (Input.NoInput)))
        (#let output Output (#call forward ((storage (#borrow-mut storage)))))
        (#let answer #u64 (#match output
          (#case (Output.NoOutput) (#block
            (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64)) 42u64))
          (#case (Output.HasOutput owner) (#block
            (#let view (#pin-ref #u64) (#pin-own-borrow (#borrow owner)))
            (#let answer #u64 (#deref view)) (#forget view)
            (#let retired (#ptr-mut #u64) (#unsafe (#pin-release owner)))
            (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (retired 4096usize))) 0i64)) answer))))
        (#forget storage) (#return answer))";
    let occupied = source.replace(
        "(Input.NoInput)))",
        "(Input.HasInput (#unsafe (#pin-own-of pointer 42u64)))))",
    );
    lim::parse(&occupied).expect("occupied owned-input fixture parses");
    run(source);
    run(&occupied);
    let retained_view = occupied.replace("(#forget view)", "");
    assert_eq!(
        compile(&retained_view).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let retired = occupied.replace(
        "(#let output",
        "(#unsafe (#word-forget Input (#borrow-slice-mut (#get storage words)))) (#let output",
    );
    let error = compile(&retired).unwrap_err();
    assert!(
        error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn optional_word_outputs_preserve_absent_concrete_input_sources() {
    let source = "(#enum Input () ((Input.NoInput) (Input.HasInput (#ref #u64))))
      (#enum Output () ((Output.NoOutput) (Output.HasOutput (#ref #u64))))
      (#struct Words () ((words (#array #u64 2))))
      (#fn convert ((storage (#ref-mut Words))) Output
        (#let input Input (#unsafe (#word-take Input (#borrow-slice-mut (#get storage words)))))
        (#return (#match input (#case (Input.NoInput) (Output.NoOutput))
          (#case (Input.HasInput view) (Output.HasOutput view)))))
      (#fn main () #u64
        (#let-mut amount #u64 42u64)
        (#let-mut storage Words (#struct-literal Words ((words (#array-repeat 0u64)))))
        (#unsafe (#word-write Input (#borrow-slice-mut (#get storage words)) (Input.NoInput)))
        (#let output Output (#call convert ((storage (#borrow-mut storage)))))
        (#let answer #u64 (#match output (#case (Output.NoOutput) 42u64)
          (#case (Output.HasOutput view) (#deref view))))
        (#forget storage) (#return answer))";
    run(source);
    let occupied = source.replace("(Input.NoInput)))", "(Input.HasInput (#borrow amount))))");
    run(&occupied);
    run(&source.replace("(#let answer", "(#set amount 0u64) (#let answer"));
    assert_eq!(
        compile(&occupied.replace("(#let answer", "(#set amount 0u64) (#let answer"))
            .unwrap_err()
            .code,
        DiagnosticCode::Borrow
    );
    for invalid in [
        source.replace(
            "(#unsafe (#word-write Input (#borrow-slice-mut (#get storage words)) (Input.NoInput)))",
            "",
        ),
        occupied.replace(
            "(#let output",
            "(#unsafe (#word-forget Input (#borrow-slice-mut (#get storage words)))) (#let output",
        ),
    ] {
        let error = compile(&invalid).unwrap_err();
        assert!(
            error.message.contains("missing required input loan")
                || error.message.contains("unresolved call inputs"),
            "{error:?}"
        );
    }
}

#[test]
fn optional_owned_word_outputs_do_not_require_impossible_payloads() {
    let source = "(#enum Input () ((Input.NoInput) (Input.HasInput (#ref #u64))))
      (#enum Output () ((Output.NoOutput) (Output.HasOutput (#ref #u64))))
      (#struct Words () ((state #u64) (words (#array #u64 2))))
      (#fn convert ((storage Words)) Output
        (#let output Output (#match (#get storage state)
          (#case 0 (Output.NoOutput))
          (#case _ (#match (#unsafe (#word-read Input (#borrow-slice (#get storage words))))
            (#case (Input.NoInput) (Output.NoOutput))
            (#case (Input.HasInput view) (Output.HasOutput view))))))
        (#forget storage) (#return output))
      (#fn main () #u64
        (#let-mut amount #u64 42u64)
        (#let-mut storage Words (#struct-literal Words
          ((state 0u64) (words (#array-repeat 0u64)))))
        (#let output Output (#call convert ((storage storage))))
        (#set amount 42u64)
        (#return (#match output (#case (Output.NoOutput) 42u64)
          (#case (Output.HasOutput view) (#deref view)))))";
    run(source);
    let occupied = source
        .replace("(state 0u64)", "(state 1u64)")
        .replace("(#let output Output (#call convert", "(#unsafe (#word-write Input (#borrow-slice-mut (#get storage words)) (Input.HasInput (#borrow amount)))) (#let output Output (#call convert")
        .replace("(#set amount 42u64)", "");
    run(&occupied);
    assert_eq!(
        compile(&occupied.replace(
            "(#return (#match output",
            "(#set amount 0u64) (#return (#match output"
        ))
        .unwrap_err()
        .code,
        DiagnosticCode::Borrow
    );
    // Excluding an impossible output never licenses the actual word reader.
    let invalid = source.replace("(state 0u64)", "(state 1u64)");
    let error = compile(&invalid).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("input loan") || error.message.contains("unresolved"),
        "{error:?}"
    );
}

#[test]
fn absent_owned_mutation_payloads_preserve_disjoint_word_selectors() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((state #u64) (words (#array #u64 1))))
      (#enum Handle () ((Handle.Empty) (Handle.Full (#ref-mut #u64))))
      (#fn empty () Handle (#return (Handle.Empty)))
      (#fn mutate ((handle Handle)) ()
        (#match handle (#case (Handle.Empty) ())
          (#case (Handle.Full target) (#block (#deref-set target 1u64) (#forget target) ())))
        (#return ()))
      (#fn read ((frame (#ref Frame))) #u64
        (#return (#match (#get frame state)
          (#case 0 42u64)
          (#case _ (#block
            (#let value Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
            (#let answer #u64 (#deref (#get value value))) (#forget value) answer)))))
      (#fn main () #u64
        (#let-mut frame Frame (#struct-literal Frame ((state 0u64) (words (#array-repeat 0u64)))))
        (#call mutate ((handle (#call empty ()))))
        (#let answer #u64 (#call read ((frame (#borrow frame)))))
        (#forget frame) (#return answer))";
    run(source);
    let invalid = source.replace(
        "(#call empty ())",
        "(Handle.Full (#borrow-mut (#get frame state)))",
    );
    let error = compile(&invalid).unwrap_err();
    assert!(
        error.message.contains("input loan") || error.message.contains("unresolved"),
        "{error:?}"
    );
}

#[test]
fn atomic_writers_preserve_disjoint_word_selectors() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Frame () ((state #u64) (words (#array #u64 1))))
      (#fn update ((count (#ref (#atomic #u64)))) ()
        (#atomic-store count 1u64 #memory-relaxed) (#return ()))
      (#fn read ((frame (#ref Frame))) #u64
        (#return (#match (#get frame state)
          (#case 0 42u64)
          (#case _ (#block
            (#let value Holder (#unsafe (#word-read Holder (#borrow-slice (#get frame words)))))
            (#let answer #u64 (#deref (#get value value))) (#forget value) answer)))))
      (#fn main () #u64
        (#let count (#atomic #u64) (#atomic-init #u64 0u64))
        (#let frame Frame (#struct-literal Frame ((state 0u64) (words (#array-repeat 0u64)))))
        (#call update ((count (#borrow count))))
        (#let answer #u64 (#call read ((frame (#borrow frame)))))
        (#forget count) (#forget frame) (#return answer))";
    run(source);
    for operation in [
        "(#atomic-fetch-add count 1u64 #memory-relaxed)",
        "(#atomic-exchange count 1u64 #memory-relaxed)",
    ] {
        run(&source.replace(
            "(#atomic-store count 1u64 #memory-relaxed)",
            &format!("(#let ignored #u64 {operation})"),
        ));
    }
    for operation in ["atomic-compare-exchange", "atomic-compare-exchange-weak"] {
        run(&source.replace(
            "(#atomic-store count 1u64 #memory-relaxed)",
            &format!("(#let ignored (#tuple #bool #u64) (#{operation} count 0u64 1u64 #memory-relaxed #memory-relaxed)) (#forget ignored)"),
        ));
    }
}

#[test]
fn helper_retirement_does_not_hide_later_byte_mutations() {
    let source = OPTIONAL_WORD_READER
        .replace(
            "(#fn main",
            "(#fn prepare ((words (#slice-mut #u64))) ()
           (#unsafe (#word-write Cell (#slice-mut-range words 0usize 2usize) (Cell.Vacant)))
           (#unsafe (#word-forget Cell words)) (#return ()))
         (#fn main",
        )
        .replace(
            "(#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))",
            "(#call prepare ((words (#borrow-slice-mut words))))",
        );
    run(&source);
    for mutation in [
        "(#unsafe (#word-write #u64 (#slice-mut-range words 0usize 1usize) 0u64))",
        "(#if #true (#unsafe (#word-write #u64 (#slice-mut-range words 0usize 1usize) 0u64)) ())",
        "(#let pointer (#ptr-mut #u64) (#ref-ptr (#slice-mut-idx words 0usize))) (#unsafe (#ptr-write pointer 0u64))",
    ] {
        let invalid = source.replace(
            "(#unsafe (#word-forget Cell words))",
            &format!("{mutation} (#unsafe (#word-forget Cell words))"),
        );
        let error = compile(&invalid).unwrap_err();
        assert!(
            error.message.contains("missing required input loan")
                || error.message.contains("unresolved call inputs"),
            "{error:?}"
        );
    }
}

#[test]
fn word_reader_entry_loans_are_conditional_on_actual_payload_tags() {
    run(OPTIONAL_WORD_READER);
    let occupied = OPTIONAL_WORD_READER.replace(
        "#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)",
        "#word-write Cell (#borrow-slice-mut words) (Cell.Occupied (#borrow amount))",
    );
    run(&occupied);
    for invalid in [
        OPTIONAL_WORD_READER.replace("(#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))", ""),
        occupied.replace("(#let answer", "(#unsafe (#word-forget Cell (#borrow-slice-mut words))) (#let answer"),
        OPTIONAL_WORD_READER.replace("(#let answer", "(#unsafe (#word-write #u64 (#borrow-slice-mut words 0usize 1usize) 0u64)) (#let answer"),
    ] {
        let error = compile(&invalid).unwrap_err();
        assert!(error.message.contains("missing required input loan") || error.message.contains("unresolved call inputs"), "{error:?}");
    }
}

#[test]
fn word_writer_may_aliases_preserve_disjoint_constructor_facts() {
    let prefix = OPTIONAL_WORD_READER.split("(#fn main").next().unwrap();
    let source = format!("{prefix}
      (#fn write-other ((words (#slice-mut #u64))) ()
        (#unsafe (#word-write #u64 words 99u64)) (#return ()))
      (#fn choose ((flag #bool)) #u64
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#let-mut second (#array #u64 1) (#array-repeat 0u64))
        (#let-mut third (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))
        (#call write-other ((words (#if flag (#borrow-slice-mut second) (#borrow-slice-mut third)))))
        (#let discard #u64 0u64) (#forget discard)
        (#let answer #u64 (#call inspect ((words (#borrow-slice words)))))
        (#forget words) (#forget second) (#forget third) (#return answer))
      (#fn main () #u64 (#return (#call choose ((flag true)))))");
    run(&source);
    run(&source.replace("((flag true))", "((flag false))"));
    let overlapping = source.replace("(#borrow-slice-mut second)", "(#borrow-slice-mut words)");
    let error = compile(&overlapping)
        .expect_err("every possible written alias must invalidate overlapping tag facts");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn word_reader_forwards_payload_conditions_through_checked_helpers() {
    let source = OPTIONAL_WORD_READER.replace("(#fn main", "(#fn forward ((words (#slice #u64))) #u64 (#return (#call inspect ((words words))))) (#fn main")
        .replace("#call inspect ((words (#borrow-slice words)))", "#call forward ((words (#borrow-slice words)))");
    run(&source);
    let invalid = source.replace(
        "(#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))",
        "",
    );
    assert!(compile(&invalid).is_err());
}

#[test]
fn guarded_word_readers_check_each_address_and_exact_enum_identity() {
    let prefix = OPTIONAL_WORD_READER.split("(#fn main").next().unwrap();
    let source = format!(
        "{prefix}
      (#fn choose ((flag #bool)) #u64
        (#let amount #u64 42u64)
        (#let-mut first (#array #u64 2) (#array-repeat 0u64))
        (#let-mut second (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Cell (#borrow-slice-mut first) (Cell.Vacant)))
        (#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Vacant)))
        (#let words (#slice #u64) (#if flag (#borrow-slice first) (#borrow-slice second)))
        (#let answer #u64 (#call inspect ((words words))))
        (#forget words) (#forget first) (#forget second) (#return answer))
      (#fn main () #u64 (#return (#call choose ((flag false)))))"
    );
    run(&source);
    let unknown = source.replace(
        "(#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Vacant)))",
        "",
    );
    assert!(compile(&unknown).is_err());
    let occupied = source.replace("(#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Vacant)))", "(#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Occupied (#borrow amount)))) (#unsafe (#word-forget Cell (#borrow-slice-mut second)))");
    assert!(compile(&occupied).is_err());
    let wrong_type = OPTIONAL_WORD_READER
        .replace(
            "(#fn main",
            "(#enum Other () ((OtherVacant) (OtherOccupied (#ref #u64)))) (#fn main",
        )
        .replace(
            "#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)",
            "#word-write Other (#borrow-slice-mut words) (OtherVacant)",
        );
    assert!(compile(&wrong_type).is_err());
}

#[test]
fn guarded_word_reader_conditions_follow_static_argument_ranges() {
    let source = OPTIONAL_WORD_READER
        .replace("(#array #u64 2)", "(#array #u64 4)")
        .replace(
            "#word-write Cell (#borrow-slice-mut words)",
            "#word-write Cell (#borrow-slice-mut words 1usize 3usize)",
        )
        .replace(
            "#call inspect ((words (#borrow-slice words)))",
            "#call inspect ((words (#borrow-slice words 1usize 3usize)))",
        );
    run(&source);
    let wrong_cell = source.replace(
        "#call inspect ((words (#borrow-slice words 1usize 3usize)))",
        "#call inspect ((words (#borrow-slice words 0usize 2usize)))",
    );
    assert!(compile(&wrong_cell).is_err());
}

#[test]
fn opaque_word_addresses_cannot_waive_payload_entry_loans() {
    let source = OPTIONAL_WORD_READER.replace("(#let answer", "(#let anchor (#ref (#array #u64 2)) (#borrow words)) (#let pointer (#ptr (#array #u64 2)) (#unsafe (#ptr-offset (#ref-ptr anchor) 0usize))) (#let opaque (#ref (#array #u64 2)) (#unsafe (#ptr-borrow anchor pointer))) (#let answer")
        .replace("#call inspect ((words (#borrow-slice words)))", "#call inspect ((words (#slice-of opaque)))")
        .replace("(#forget words)", "(#forget opaque) (#forget anchor) (#forget words)");
    assert!(compile(&source).is_err());
}

#[test]
fn disjoint_metadata_writes_preserve_entry_tag_conditions() {
    let prefix = OPTIONAL_WORD_READER.split("(#fn main").next().unwrap();
    let source = format!("{prefix}
      (#struct Buffer () ((counter #u64) (words (#array #u64 2))))
      (#fn update-and-read ((buffer (#ref-mut Buffer))) #u64
        (#deref-set (#borrow-mut (#get buffer counter)) 1u64)
        (#return (#call inspect ((words (#borrow-slice (#get buffer words)))))))
      (#fn main () #u64
        (#let-mut buffer Buffer (#struct-literal Buffer ((counter 0u64) (words (#array-repeat 0u64)))))
        (#unsafe (#word-write Cell (#borrow-slice-mut (#get buffer words)) (Cell.Vacant)))
        (#let answer #u64 (#call update-and-read ((buffer (#borrow-mut buffer)))))
        (#assert (#u64::eq (#get buffer counter) 1u64))
        (#forget buffer) (#return answer))");
    run(&source);
    let invalid = source.replace(
        "(#deref-set (#borrow-mut (#get buffer counter)) 1u64)",
        "(#deref-set (#borrow-mut (#index (#get buffer words) 0usize)) 1u64)",
    );
    assert!(compile(&invalid).is_err());
}

#[test]
fn word_reader_cannot_reuse_an_entry_tag_after_mutating_its_bytes() {
    let source = OPTIONAL_WORD_READER.replace("((words (#slice #u64)))", "((words (#ref-mut (#array #u64 2))))")
        .replace("(#let cell Cell", "(#unsafe (#word-write #u64 (#borrow-slice-mut (#deref words) 0usize 1usize) 1u64)) (#let cell Cell")
        .replace("#word-read Cell words", "#word-read Cell (#borrow-slice (#deref words))")
        .replace("#call inspect ((words (#borrow-slice words)))", "#call inspect ((words (#borrow-mut words)))");
    let error = compile(&source).unwrap_err();
    assert!(
        error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn actual_empty_constructor_does_not_require_inactive_word_reference() {
    run(EMPTY_REFERENCE_CELL);
    for operation in ["word-read", "word-view"] {
        let source = if operation == "word-read" {
            EMPTY_REFERENCE_CELL.replace(
                "#word-take Cell (#borrow-slice-mut words)",
                "#word-read Cell (#borrow-slice words)",
            )
        } else {
            EMPTY_REFERENCE_CELL
                .replace("(#let cell Cell", "(#let cell (#ref Cell)")
                .replace(
                    "#word-take Cell (#borrow-slice-mut words)",
                    "#word-view (#ref Cell) (#borrow-slice words)",
                )
        };
        run(&source);
    }
}

#[test]
fn numeric_zero_is_not_an_empty_constructor_witness() {
    let source = EMPTY_REFERENCE_CELL
        .replace("(#let cell Cell", "(#let cell (#ref Cell)")
        .replace(
            "#word-take Cell (#borrow-slice-mut words)",
            "#word-view (#ref Cell) (#borrow-slice words)",
        );
    let no_write = source.replace(
        "(#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)))",
        "",
    );
    let error = compile(&no_write).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing slot provenance"),
        "{error:?}"
    );
    let overwritten = source.replace(
        "(#let cell",
        "(#unsafe (#word-write #u64 (#borrow-slice-mut words 0usize 1usize) 0u64)) (#let cell",
    );
    let error = compile(&overwritten).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing slot provenance"),
        "{error:?}"
    );
}

#[test]
fn nested_constructor_facts_use_nonzero_backing_offsets_and_enum_identity() {
    let source = "(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
      (#enum Outer () ((Outer.Absent) (Outer.Present Cell)))
      (#struct Holder () ((prefix #u64) (cell Outer) (suffix #u64)))
      (#fn main () #u64
        (#let-mut words (#array #u64 7) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 6usize)
          (#struct-literal Holder ((prefix 40u64) (cell (Outer.Present (Cell.Vacant))) (suffix 2u64)))))
        (#let value Holder (#unsafe (#word-take Holder (#borrow-slice-mut words 1usize 6usize))))
        (#let answer #u64 (#u64::add-wrap (#get value prefix) (#get value suffix)))
        (#forget value) (#return answer))";
    run(source);
    let lost_outer = source.replace("(#let value Holder", "(#unsafe (#word-write #u64 (#borrow-slice-mut words 2usize 3usize) 1u64)) (#let value Holder");
    assert!(compile(&lost_outer)
        .unwrap_err()
        .message
        .contains("missing slot provenance"));
    let wrong_type = EMPTY_REFERENCE_CELL
        .replace(
            "(#fn main",
            "(#enum Other () ((OtherVacant) (OtherOccupied (#ref #u64)))) (#fn main",
        )
        .replace(
            "#word-write Cell (#borrow-slice-mut words) (Cell.Vacant)",
            "#word-write Other (#borrow-slice-mut words) (OtherVacant)",
        );
    assert!(compile(&wrong_type)
        .unwrap_err()
        .message
        .contains("missing slot provenance"));
}

#[test]
fn occupied_word_cells_need_real_reference_provenance_after_retirement() {
    let source = "(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
      (#fn main () #u64
        (#let amount #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Occupied (#borrow amount))))
        (#let view (#ref Cell) (#unsafe (#word-view (#ref Cell) (#borrow-slice words))))
        (#forget view)
        (#unsafe (#word-forget Cell (#borrow-slice-mut words)))
        (#return 42u64))";
    run(source);
    let retired = source.replace("(#return 42u64)", "(#let invalid (#ref Cell) (#unsafe (#word-view (#ref Cell) (#borrow-slice words)))) (#forget invalid) (#return 42u64)");
    assert!(compile(&retired)
        .unwrap_err()
        .message
        .contains("missing slot provenance"));
    let cleared = retired.replace(
        "(#let invalid",
        "(#unsafe (#word-write Cell (#borrow-slice-mut words) (Cell.Vacant))) (#let invalid",
    );
    run(&cleared);
}

#[test]
fn constructor_facts_are_per_cell_and_required_on_every_reaching_address() {
    let source = "(#enum Cell () ((Cell.Vacant) (Cell.Occupied (#ref #u64))))
      (#fn choose ((flag #bool)) #u64
        (#let amount #u64 42u64)
        (#let-mut first (#array #u64 2) (#array-repeat 0u64))
        (#let-mut second (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Cell (#borrow-slice-mut first) (Cell.Vacant)))
        (#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Vacant)))
        (#let words (#slice #u64) (#if flag (#borrow-slice first) (#borrow-slice second)))
        (#let view (#ref Cell) (#unsafe (#word-view (#ref Cell) words)))
        (#forget view) (#forget words) (#return 42u64))
      (#fn main () #u64 (#return (#call choose ((flag true)))))";
    run(source);
    let unknown = source.replace(
        "(#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Vacant)))",
        "",
    );
    assert!(compile(&unknown)
        .unwrap_err()
        .message
        .contains("missing slot provenance"));
    let occupied = source.replace("(#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Vacant)))", "(#unsafe (#word-write Cell (#borrow-slice-mut second) (Cell.Occupied (#borrow amount)))) (#unsafe (#word-forget Cell (#borrow-slice-mut second)))");
    assert!(compile(&occupied)
        .unwrap_err()
        .message
        .contains("missing slot provenance"));
    let independent = occupied.replace(
        "(#if flag (#borrow-slice first) (#borrow-slice second))",
        "(#borrow-slice first)",
    );
    run(&independent);
}

#[test]
fn raw_mutation_invalidates_word_constructor_facts() {
    let source = EMPTY_REFERENCE_CELL
        .replace("(#let cell Cell", "(#let cell (#ref Cell)")
        .replace(
            "#word-take Cell (#borrow-slice-mut words)",
            "#word-view (#ref Cell) (#borrow-slice words)",
        );
    let invalid = source.replace("(#let cell", "(#let pointer (#ptr-mut #u64) (#ref-ptr (#borrow-mut (#index words 0usize)))) (#unsafe (#ptr-write pointer 0u64)) (#let cell");
    assert!(compile(&invalid)
        .unwrap_err()
        .message
        .contains("missing slot provenance"));
    let retired_empty = source.replace(
        "(#let cell",
        "(#unsafe (#word-forget Cell (#borrow-slice-mut words))) (#let cell",
    );
    run(&retired_empty);
}

const REFERENCE_WORDS: &str = "
(#struct Pair () ((left #u8) (right #u64)))
(#fn expose ((value (#pin-ref-mut Pair))) (#slice-mut #u64)
  (#return (#unsafe (#word-view (#slice-mut #u64) value))))
(#fn main () #u64
  (#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 40u64 2u64))
  (#let target (#pin-ref-mut Pair)
    (#unsafe (#word-view (#pin-ref-mut Pair) (#borrow-slice-mut words))))
  (#let raw (#slice-mut #u64) (#call expose ((value target))))
  (#assert (#usize::eq (#slice-mut-len raw) 2usize))
  (#unsafe (#word-write Pair raw (#struct-literal Pair ((left 20u8) (right 22u64)))))
  (#let raw-read (#slice #u64) (#unsafe (#word-view (#slice #u64) target)))
  (#let result Pair (#unsafe (#word-read Pair raw-read)))
  (#forget raw-read) (#forget target)
  (#let answer #u64 (#u64::add-wrap (#as (#get result left) #u64) (#get result right)))
  (#forget result) (#return answer))";

#[test]
fn reference_word_views_preserve_selected_stack_layout_and_helper_lifetimes() {
    run(REFERENCE_WORDS);
    let conflict = REFERENCE_WORDS.replace(
        "(#let result Pair",
        "(#set-index words 0usize 99u64) (#let result Pair",
    );
    assert_eq!(compile(&conflict).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn reference_word_views_preserve_heap_layout_and_owner_lifetimes() {
    let source = REFERENCE_WORDS
        .replace(
            "(#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 40u64 2u64))",
            "(#let pointer (#ptr-mut (#array #u64 2))
          (#unsafe (#linux-syscall (#ptr-mut (#array #u64 2)) 9usize
            (0usize 16usize 3usize 34usize -1i64 0usize))))
         (#let-mut owner (#pin-own (#array #u64 2))
          (#unsafe (#pin-own-of pointer (#array-of (#array #u64 2) 40u64 2u64))))",
        )
        .replace(
            "(#borrow-slice-mut words)",
            "(#unsafe (#word-view (#slice-mut #u64) (#pin-own-borrow-mut owner)))",
        )
        .replace(
            "(#forget raw-read) (#forget target)",
            "(#forget raw-read) (#forget target)
         (#let pointer-out (#ptr-mut (#array #u64 2)) (#unsafe (#pin-release owner)))
         (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer-out 16usize))) 0i64))",
        );
    run(&source);
    let invalid = source.replace("(#forget raw-read) (#forget target)", "");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn reference_word_views_check_unsafe_mutability_types_and_escapes() {
    let missing = REFERENCE_WORDS.replace(
        "(#unsafe (#word-view (#slice-mut #u64) value))",
        "(#word-view (#slice-mut #u64) value)",
    );
    assert_eq!(compile(&missing).unwrap_err().code, DiagnosticCode::Unsafe);
    let immutable = REFERENCE_WORDS.replace("(#pin-ref-mut Pair)", "(#pin-ref Pair)");
    assert_eq!(
        compile(&immutable).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let wrong_element = REFERENCE_WORDS.replace("(#slice-mut #u64)", "(#slice-mut #u8)");
    assert_eq!(
        compile(&wrong_element).unwrap_err().code,
        DiagnosticCode::Type
    );
    let escape = "(#fn bad () (#slice #u64)
      (#let value #u64 42u64)
      (#return (#unsafe (#word-view (#slice #u64) (#borrow value)))))";
    assert_eq!(compile(escape).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn word_staging_preserves_observable_clone_hooks() {
    let source = "(#struct Value () ((number #u64) (count (#ptr-mut #u64))))
      (#fn Value::clone ((value Value)) Value
        (#unsafe (#ptr-write (#get value count)
          (#u64::add-wrap (#ptr-read (#get value count)) 1u64))) (#return value))
      (#fn main () #u64
        (#let-mut count #u64 0u64)
        (#let pointer (#ptr-mut #u64) (#ref-ptr (#borrow-mut count)))
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#let initial Value (#struct-literal Value ((number 40u64) (count pointer))))
        (#unsafe (#word-write Value (#borrow-slice-mut words) initial))
        (#let source Value (#unsafe (#word-read Value (#borrow-slice words))))
        (#let copied Value (#block (#let nested Value source) (#clone nested)))
        (#unsafe (#word-write Value (#borrow-slice-mut words)
          (#block (#let staged Value copied) (#clone staged))))
        (#assert (#u64::eq count 2u64))
        (#let result Value (#unsafe (#word-read Value (#borrow-slice words))))
        (#return (#u64::add-wrap (#get result number) count)))";
    run(source);
    let large = source
        .replace(
            "((number #u64) (count (#ptr-mut #u64)))",
            "((number #u64) (count (#ptr-mut #u64))
              (a #u64) (b #u64) (c #u64) (d #u64) (e #u64))",
        )
        .replace("(#array #u64 2)", "(#array #u64 7)")
        .replace(
            "((number 40u64) (count pointer))",
            "((number 40u64) (count pointer)
              (a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64))",
        );
    run(&large);
}

#[test]
fn zero_word_markers_do_not_exhaust_native_return_registers() {
    run("(#struct Marked () ((number #u64)
        (a (#array #u64 0)) (b (#array #u64 0)) (c (#array #u64 0))
        (d (#array #u64 0)) (e (#array #u64 0)) (f (#array #u64 0))))
      (#fn make () Marked
        (#return (#struct-literal Marked ((number 42u64)
          (a (#array-of (#array #u64 0))) (b (#array-of (#array #u64 0)))
          (c (#array-of (#array #u64 0))) (d (#array-of (#array #u64 0)))
          (e (#array-of (#array #u64 0))) (f (#array-of (#array #u64 0)))))))
      (#fn main () #u64 (#let value Marked (#call make ()))
        (#return (#get value number)))");
}

#[test]
fn releasing_owned_storage_ends_only_its_contained_handles() {
    let source = "(#struct Owner () ((number #u64) (words (#array #u64 1))))
      (#fn main () #u64
        (#let-mut owner Owner (#struct-literal Owner
          ((number 42u64) (words (#array-repeat 0u64)))))
        (#unsafe (#word-write (#ref #u64) (#borrow-slice-mut (#get owner words))
          (#borrow (#get owner number))))
        (#forget owner) (#return 42u64))";
    run(source);
    let inspected = format!(
        "(#fn inspect ((owner (#pin-ref Owner))) #u64
      (#return (#get owner number)))\n{source}"
    )
    .replace(
        "(#forget owner) (#return 42u64)",
        "(#let answer #u64 (#call inspect ((owner (#pin-borrow owner)))))
         (#forget owner) (#return answer)",
    );
    run(&inspected);
    let escaped = source.replace(
        "(#forget owner) (#return 42u64)",
        "(#let view (#ref #u64) (#unsafe (#word-read (#ref #u64)
           (#borrow-slice (#get owner words)))))
         (#forget owner) (#return (#deref view))",
    );
    assert_eq!(compile(&escaped).unwrap_err().code, DiagnosticCode::Borrow);
    let sibling = source.replace(
        "(#forget owner)",
        "(#forget (#get owner number)) (#forget owner)",
    );
    assert_eq!(compile(&sibling).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn word_take_transfers_reference_ownership_and_retires_source_provenance() {
    let source = "(#struct Holder () ((view (#ref-mut #u64))))
      (#fn main () #u64
        (#let-mut seed #u64 40u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((view (#borrow-mut seed))))))
        (#let holder Holder (#unsafe (#word-take Holder (#borrow-slice-mut words))))
        (#let view (#ref-mut #u64) (#get holder view))
        (#forget holder) (#forget words)
        (#deref-set view 42u64)
        (#let answer #u64 (#deref view))
        (#forget view) (#return answer))";
    run(source);
    let repeated = source.replace(
        "(#let view",
        "(#let again Holder (#unsafe (#word-take Holder (#borrow-slice-mut words))))
         (#forget again) (#let view",
    );
    assert_eq!(compile(&repeated).unwrap_err().code, DiagnosticCode::Linear);
    let shared = source.replace(
        "(#word-take Holder (#borrow-slice-mut words))",
        "(#word-take Holder (#borrow-slice words))",
    );
    assert_eq!(compile(&shared).unwrap_err().code, DiagnosticCode::Borrow);
    let safe = source.replace("(#unsafe (#word-take", "(#block (#word-take");
    assert_eq!(compile(&safe).unwrap_err().code, DiagnosticCode::Unsafe);
    let alias = source.replace("(#deref-set view", "(#set seed 0u64) (#deref-set view");
    assert_eq!(compile(&alias).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn nested_word_view_field_addresses_keep_external_pointees_separate() {
    let source = "(#struct Inner () ((value (#ref #u64))))
      (#struct Outer () ((inner Inner)))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Outer (#borrow-slice-mut words)
          (#struct-literal Outer ((inner
            (#struct-literal Inner ((value (#borrow seed)))))))))
        (#let owner (#pin-ref Outer) (#unsafe
          (#word-view (#pin-ref Outer) (#borrow-slice words))))
        (#let field (#pin-ref Inner) (#pin-borrow (#get owner inner)))
        (#let slot (#pin-ref (#ref #u64)) (#pin-borrow (#get field value)))
        (#let restored (#ref #u64) (#deref slot))
        (#let answer #u64 (#deref restored))
        (#forget restored) (#forget slot) (#forget field) (#forget owner)
        (#forget words) (#return answer))";
    run(source);
    let helpers = "(#fn field ((owner (#pin-ref Outer))) (#pin-ref Inner)
        (#return (#pin-borrow (#get owner inner))))
      (#fn forwarded ((owner (#pin-ref Outer))) (#pin-ref Inner)
        (#return (#call field ((owner owner)))))";
    let forwarded = format!("{helpers}\n{source}").replace(
        "(#pin-borrow (#get owner inner)))\n        (#let slot",
        "(#call forwarded ((owner owner))))\n        (#let slot",
    );
    assert_ne!(forwarded, format!("{helpers}\n{source}"));
    run(&forwarded);
    let invalid = forwarded.replace("(#let answer", "(#set seed 0u64) (#let answer");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
    let untracked_forwarded = forwarded.replace(
        "(#unsafe (#word-write Outer (#borrow-slice-mut words)
          (#struct-literal Outer ((inner
            (#struct-literal Inner ((value (#borrow seed)))))))))",
        "(#unsafe (#word-write #u64 (#borrow-slice-mut words) 0u64))",
    );
    assert_eq!(
        compile(&untracked_forwarded).unwrap_err().code,
        DiagnosticCode::Linear
    );
    for invalid in [
        source.replace("(#let answer", "(#set seed 0u64) (#let answer"),
        source
            .replace("(#let restored", "(#forget words) (#let restored")
            .replace("(#forget words) (#return answer)", "(#return answer)"),
    ] {
        let error = compile(&invalid).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    }
    let untracked = source.replace(
        "(#unsafe (#word-write Outer (#borrow-slice-mut words)
          (#struct-literal Outer ((inner
            (#struct-literal Inner ((value (#borrow seed)))))))))",
        "(#unsafe (#word-write #u64 (#borrow-slice-mut words) 0u64))",
    );
    let error = compile(&untracked).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(error.message.contains("provenance"), "{error:?}");

    // Pinning the container does not pin its stored ordinary reference.
    let upgraded = source.replace(
        "(#let restored (#ref #u64)",
        "(#let restored (#pin-ref #u64)",
    );
    assert_eq!(compile(&upgraded).unwrap_err().code, DiagnosticCode::Type);
}

#[test]
fn typed_reference_holder_lends_its_word_view_without_duplicating_the_loan() {
    let source = "(#struct Holder () ((view (#ref-mut #u64))))
      (#fn touch ((target (#ref-mut #u64))) ()
        (#deref-set target (#u64::add-wrap (#deref target) 1u64)) (#return ()))
      (#fn main () #u64
        (#let-mut words (#array #u64 1) (#array-of (#array #u64 1) 40u64))
        (#let view (#ref-mut #u64) (#unsafe (#word-view (#ref-mut #u64)
          (#block
            (#let anchor (#ref-mut (#array #u64 1)) (#borrow-mut words))
            (#borrow-slice-mut (#deref anchor))))))
        (#let-mut holder Holder (#struct-literal Holder ((view view))))
        (#call touch ((target (#deref (#borrow-mut (#get holder view))))))
        (#call touch ((target (#deref (#borrow-mut (#get holder view))))))
        (#let result #u64 (#deref (#get holder view)))
        (#forget holder) (#return result))";
    run(source);
    let through_owner = source
        .replace(
            "(#let-mut holder Holder (#struct-literal Holder ((view view))))",
            "(#let-mut holder Holder (#struct-literal Holder ((view view))))
           (#let owner-view (#ref-mut Holder) (#borrow-mut holder))",
        )
        .replace("(#get holder view)", "(#get owner-view view)")
        .replace("(#forget holder)", "(#forget owner-view) (#forget holder)");
    run(&through_owner);
    let conflict = through_owner
        .replacen(
            "(#call touch",
            "
      (#let child (#ref #u64) (#borrow (#deref (#get owner-view view))))
      (#call touch",
            1,
        )
        .replace(
            "(#forget owner-view)",
            "(#forget child) (#forget owner-view)",
        );
    let error = compile(&conflict).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Borrow, "{}", error.message);
}

#[test]
fn word_view_outlives_temporary_anchor_but_not_its_parameter() {
    let source = "(#fn read ((words (#ref-mut (#array #u64 2)))) #u64
      (#let selected (#ref #u64) (#unsafe (#word-view (#ref #u64)
        (#block
          (#let anchor (#ref (#array #u64 2)) (#borrow (#deref words)))
          (#borrow-slice (#deref anchor) 0usize 1usize)))))
      (#let again (#ref #u64) selected)
      (#return (#u64::add-wrap (#deref selected) (#deref again))))
      (#fn main () #u64
        (#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 21u64 0u64))
        (#return (#call read ((words (#borrow-mut words))))))";
    run(source);
    let conflict = source.replace(
        "(#let again",
        "(#deref-set words (#array-of (#array #u64 2) 99u64 0u64)) (#let again",
    );
    assert_eq!(compile(&conflict).unwrap_err().code, DiagnosticCode::Borrow);
    let exclusive = source
        .replace(
            "(#let selected (#ref #u64)",
            "(#let selected (#ref-mut #u64)",
        )
        .replacen("#word-view (#ref #u64)", "#word-view (#ref-mut #u64)", 1)
        .replace(
            "(#let anchor (#ref (#array #u64 2)) (#borrow (#deref words)))",
            "(#let anchor (#ref-mut (#array #u64 2)) (#borrow-mut (#deref words)))",
        )
        .replace(
            "(#borrow-slice (#deref anchor)",
            "(#borrow-slice-mut (#deref anchor)",
        )
        .replace(
            "(#let again (#ref #u64) selected)",
            "(#let again (#ref #u64) (#borrow (#index (#deref words) 0usize)))",
        );
    assert_eq!(
        compile(&exclusive).unwrap_err().code,
        DiagnosticCode::Borrow
    );
}

#[test]
fn word_view_uses_result_mutability_without_losing_alias_protection() {
    let shared = SOURCE
        .replace("(#borrow-slice words)", "(#borrow-slice-mut words)")
        .replace(
            "(#let result",
            "(#let observed #u64 (#index words 0usize)) (#let result",
        );
    run(&shared);
    let conflicting_write = shared.replace(
        "(#let observed",
        "(#set-index words 0usize 99u64) (#let observed",
    );
    assert_eq!(
        compile(&conflicting_write).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let exclusive = shared
        .replace("(#let view (#ref Pair)", "(#let view (#ref-mut Pair)")
        .replace("#word-view (#ref Pair)", "#word-view (#ref-mut Pair)")
        .replace("((pair (#ref Pair)))", "((pair (#ref-mut Pair)))");
    assert_eq!(
        compile(&exclusive).unwrap_err().code,
        DiagnosticCode::Borrow
    );
}

#[test]
fn word_access_checks_unsafe_types_aliases_and_lifetimes() {
    let missing = SOURCE.replace(
        "(#unsafe (#word-view (#ref Pair) (#borrow-slice words)))",
        "(#word-view (#ref Pair) (#borrow-slice words))",
    );
    let error = compile(&missing).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Unsafe, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&missing[span.start..span.end], "#word-view");
    let overlap = SOURCE.replace(
        "(#let result",
        "(#set-index words 0usize 99u64) (#let result",
    );
    assert_eq!(compile(&overlap).unwrap_err().code, DiagnosticCode::Borrow);
    let escaping = "(#fn bad () (#ref #u64)
      (#let words (#array #u64 1) (#array-of (#array #u64 1) 42u64))
      (#return (#unsafe (#word-view (#ref #u64) (#borrow-slice words)))))";
    assert_eq!(compile(escaping).unwrap_err().code, DiagnosticCode::Borrow);
    let shared = SOURCE
        .replace("#word-view (#ref Pair)", "#word-view (#ref-mut Pair)")
        .replace("(#let view (#ref Pair)", "(#let view (#ref-mut Pair)");
    assert_eq!(compile(&shared).unwrap_err().code, DiagnosticCode::Borrow);
    let incorrect_value = SOURCE.replace("left 40u8", "left 40u64");
    assert_eq!(
        compile(&incorrect_value).unwrap_err().code,
        DiagnosticCode::Type
    );
    let incorrect_storage = SOURCE
        .replace("(#array #u64 2)", "(#array #u8 2)")
        .replace("(#array-repeat 0u64)", "(#array-repeat 0u8)");
    assert_eq!(
        compile(&incorrect_storage).unwrap_err().code,
        DiagnosticCode::Type
    );
}

#[test]
fn word_reads_and_writes_handle_large_aggregates() {
    run("(#fn main () #u64
      (#let-mut words (#array #u64 8) (#array-repeat 0u64))
      (#unsafe (#word-write (#array #u64 8) (#borrow-slice-mut words)
        (#array-of (#array #u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 42u64)))
      (#let value (#array #u64 8) (#unsafe (#word-read (#array #u64 8) (#borrow-slice words))))
      (#return (#index value 7usize)))");
}

#[test]
fn heap_word_views_preserve_flat_not_packed_layout() {
    let source = SOURCE.replace(
        "(#let-mut words (#array #u64 2) (#array-repeat 0u64))",
        "(#let pointer (#ptr-mut (#array #u64 2))
          (#unsafe (#linux-syscall (#ptr-mut (#array #u64 2)) 9usize
            (0usize 16usize 3usize 34usize -1i64 0usize))))
         (#let-mut owner (#pin-own (#array #u64 2))
          (#unsafe (#pin-own-of pointer (#array-of (#array #u64 2) 0u64 0u64))))",
    );
    let source = source.replace("(#unsafe (#word-write", "(#let writable (#pin-ref-mut (#array #u64 2)) (#pin-own-borrow-mut owner))\n  (#unsafe (#word-write")
        .replace("(#borrow-slice-mut words)", "(#slice-mut-of (#unsafe (#ptr-borrow-mut writable (#ref-ptr writable))))")
        .replace("(#let view", "(#forget writable)\n  (#let readable (#pin-ref (#array #u64 2)) (#pin-own-borrow owner))\n  (#let view")
        .replace("(#borrow-slice words)", "(#slice-of (#unsafe (#ptr-borrow readable (#ref-ptr readable))))")
        .replace("(#forget view) (#return result)",
          "(#forget view) (#forget readable)
           (#let raw (#ptr-mut (#array #u64 2)) (#unsafe (#pin-release owner)))
           (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (raw 16usize))) 0i64))
           (#return result)");
    run(&source);
    let invalid = source.replace("(#forget view) ", "");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn disjoint_word_ranges_keep_a_sibling_address_live() {
    let source = "(#fn main () #u64
      (#let-mut words (#array #u64 2) (#array-of (#array #u64 2) 40u64 0u64))
      (#let kept (#ref #u64) (#unsafe (#word-view (#ref #u64) (#borrow-slice words 0usize 1usize))))
      (#unsafe (#word-write #u64 (#borrow-slice-mut words 1usize 2usize) 2u64))
      (#let other #u64 (#unsafe (#word-read #u64 (#borrow-slice words 1usize 2usize))))
      (#let result #u64 (#u64::add-wrap (#deref kept) other))
      (#forget kept) (#return result))";
    run(source);
    let invalid = source.replace(
        "#borrow-slice-mut words 1usize 2usize",
        "#borrow-slice-mut words 0usize 1usize",
    );
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn returned_views_retain_their_callers_storage_lifetime() {
    let source = "(#fn view ((words (#slice #u64))) (#ref #u64)
      (#return (#unsafe (#word-view (#ref #u64) words))))
    (#fn main () #u64
      (#let-mut words (#array #u64 1) (#array-of (#array #u64 1) 42u64))
      (#let selected (#ref #u64) (#call view ((words (#borrow-slice words)))))
      (#let result #u64 (#deref selected)) (#forget selected) (#return result))";
    run(source);
    let invalid = source.replace(
        "(#let result",
        "(#set-index words 0usize 99u64) (#let result",
    );
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn typed_word_view_maps_callee_consumption_to_actual_backing_regions() {
    let source = "(#struct Token (#linear) ((amount #u64)))
      (#enum Slot (#linear) ((Slot.Empty) (Slot.Full Token)))
      (#struct Buffer () ((prefix #u64) (slot Slot) (suffix #u64)))
      (#fn clear ((slot (#pin-ref-mut Slot))) ()
        (#unsafe (#forget (#pin-read slot)))
        (#unsafe (#pin-write slot (Slot.Empty))) (#return ()))
      (#fn clear-buffer ((buffer (#pin-ref-mut Buffer))) ()
        (#call clear ((slot (#pin-borrow-mut (#get buffer slot))))) (#return ()))
      (#fn main () #u64
        (#let-mut words (#array #u64 6) (#array-repeat 0u64))
        (#unsafe (#word-write Buffer (#borrow-slice-mut words 1usize 5usize)
          (#struct-literal Buffer ((prefix 40u64) (slot (Slot.Full (#struct-literal Token ((amount 7u64))))) (suffix 2u64)))))
        (#call clear-buffer ((buffer (#unsafe (#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 5usize))))))
        (#let prefix #u64 (#unsafe (#word-read #u64 (#borrow-slice words 1usize 2usize))))
        (#let suffix #u64 (#unsafe (#word-read #u64 (#borrow-slice words 4usize 5usize))))
        (#assert (#u64::eq (#unsafe (#word-read #u64 (#borrow-slice words 2usize 3usize))) 0u64))
        (#forget words) (#return (#u64::add-wrap prefix suffix)))";
    run(source);
    let short = source.replace(
        "#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 5usize)",
        "#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 3usize)",
    );
    assert!(compile(&short)
        .unwrap_err()
        .message
        .contains("unresolved call inputs"));
    let dynamic = source
        .replace(
            "(#call clear-buffer",
            "(#let start #usize 1usize) (#call clear-buffer",
        )
        .replace(
            "#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 5usize)",
            "#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words start 5usize)",
        );
    assert!(compile(&dynamic)
        .unwrap_err()
        .message
        .contains("unresolved call inputs"));
    let opaque = source
        .replace(
            "(#call clear-buffer",
            "(#let anchor (#ref-mut (#array #u64 6)) (#borrow-mut words))
         (#let pointer (#ptr-mut (#array #u64 6)) (#unsafe (#ptr-offset (#ref-ptr anchor) 0usize)))
         (#let opaque (#ref-mut (#array #u64 6)) (#unsafe (#ptr-borrow-mut anchor pointer)))
         (#drop anchor) (#call clear-buffer",
        )
        .replace(
            "#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut words 1usize 5usize)",
            "#word-view (#pin-ref-mut Buffer) (#borrow-slice-mut (#deref opaque) 1usize 5usize)",
        );
    let error = compile(&opaque).unwrap_err();
    assert!(
        error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn word_forget_retires_loans_without_loading_or_zeroing_memory() {
    let source = "(#fn main () #u64
      (#let-mut seed #u64 0u64)
      (#let-mut words (#array #u64 1) (#array-repeat 0u64))
      (#unsafe (#word-write (#ref-mut #u64) (#borrow-slice-mut words) (#borrow-mut seed)))
      (#let before #u64 (#unsafe (#word-read #u64 (#borrow-slice words))))
      (#unsafe (#word-forget (#ref-mut #u64) (#borrow-slice-mut words)))
      (#unsafe (#word-forget (#ref-mut #u64) (#borrow-slice-mut words)))
      (#let after #u64 (#unsafe (#word-read #u64 (#borrow-slice words))))
      (#assert (#u64::eq before after))
      (#set seed 42u64) (#forget words) (#return seed))";
    run(source);
    let missing = source.replace(
        "(#let after #u64 (#unsafe (#word-read #u64 (#borrow-slice words))))",
        "(#let recovered (#ref-mut #u64) (#unsafe (#word-take (#ref-mut #u64) (#borrow-slice-mut words)))) (#drop recovered) (#let after #u64 before)",
    );
    assert_eq!(compile(&missing).unwrap_err().code, DiagnosticCode::Linear);
    let shared = source.replace(
        "#word-forget (#ref-mut #u64) (#borrow-slice-mut words)",
        "#word-forget (#ref-mut #u64) (#borrow-slice words)",
    );
    assert!(compile(&shared)
        .unwrap_err()
        .message
        .contains("mutable word slice"));
    let safe = "(#fn main () #u64
      (#let-mut words (#array #u64 1) (#array-repeat 0u64))
      (#word-forget (#ref #u64) (#borrow-slice-mut words))
      (#forget words) (#return 42u64))";
    assert_eq!(compile(safe).unwrap_err().code, DiagnosticCode::Unsafe);
}

#[test]
fn retired_word_cells_can_be_reused_without_reviving_old_loans() {
    let source = "(#fn main () #u64
      (#let-mut old #u64 0u64) (#let-mut current #u64 42u64)
      (#let-mut words (#array #u64 1) (#array-repeat 0u64))
      (#unsafe (#word-write (#ref-mut #u64) (#borrow-slice-mut words) (#borrow-mut old)))
      (#unsafe (#word-forget (#array #u64 1) (#borrow-slice-mut words)))
      (#set old 1u64)
      (#unsafe (#word-write (#ref-mut #u64) (#borrow-slice-mut words) (#borrow-mut current)))
      (#set old 2u64)
      (#let restored (#ref-mut #u64) (#unsafe (#word-take (#ref-mut #u64) (#borrow-slice-mut words))))
      (#let answer #u64 (#deref restored))
      (#forget restored) (#forget words) (#return answer))";
    run(source);
    let still_borrowed = source.replace("(#set old 2u64)", "(#set current 0u64)");
    assert_eq!(
        compile(&still_borrowed).unwrap_err().code,
        DiagnosticCode::Borrow
    );
    let retired = source.replace(
        "(#let restored",
        "(#unsafe (#word-forget (#array #u64 1) (#borrow-slice-mut words))) (#let restored",
    );
    assert_eq!(compile(&retired).unwrap_err().code, DiagnosticCode::Linear);
}

#[test]
fn word_forget_does_not_end_transferred_or_neighboring_loans() {
    let source = "(#fn main () #u64
      (#let-mut seed #u64 42u64)
      (#let-mut words (#array #u64 2) (#array-repeat 0u64))
      (#unsafe (#word-write (#ref-mut #u64) (#borrow-slice-mut words 1usize 2usize) (#borrow-mut seed)))
      (#unsafe (#word-forget (#ref-mut #u64) (#borrow-slice-mut words 0usize 1usize)))
      (#set seed 0u64) (#forget words) (#return 42u64))";
    assert_eq!(compile(source).unwrap_err().code, DiagnosticCode::Borrow);
    let escaped = source.replace(
        "(#unsafe (#word-forget",
        "(#let escaped (#ref-mut #u64) (#unsafe (#word-take (#ref-mut #u64) (#borrow-slice-mut words 1usize 2usize)))) (#unsafe (#word-forget",
    ).replace("(#set seed 0u64)", "(#set seed 0u64) (#drop escaped)");
    assert_eq!(compile(&escaped).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn numeric_words_cannot_invent_reference_provenance() {
    let source = "(#struct Holder () ((item (#ref #u64))))
      (#fn bad ((words (#slice #u64))) (#ref #u64)
        (#let holder (#ref Holder) (#unsafe (#word-view (#ref Holder) words)))
        (#return (#get holder item)))
      (#fn main () #u64
        (#let words (#array #u64 1) (#array-of (#array #u64 1) 42u64))
        (#return (#deref (#call bad ((words (#borrow-slice words)))))))";
    let error = compile(source).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing slot provenance")
            || error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn typed_word_writes_preserve_contained_reference_provenance() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((value (#borrow seed))))))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let result #u64 (#deref (#get copied value)))
        (#forget copied) (#forget words) (#set seed 0u64)
        (#return result))";
    run(source);
    run(&source.replace(
        "copied Holder (#unsafe (#word-read Holder",
        "copied (#ref Holder) (#unsafe (#word-view (#ref Holder)",
    ));
    let heap = source
        .replace("(#let-mut words (#array #u64 1) (#array-repeat 0u64))",
          "(#let allocation (#ptr-mut (#array #u64 1)) (#unsafe (#linux-syscall (#ptr-mut (#array #u64 1))
            9usize (0usize 8usize 3usize 34usize -1i64 0usize))))
           (#let-mut owner (#pin-own (#array #u64 1)) (#unsafe (#pin-own-of allocation (#array-repeat 0u64))))
           (#let anchor (#pin-ref-mut (#array #u64 1)) (#pin-own-borrow-mut owner))
           (#let writable (#ref-mut (#array #u64 1)) (#unsafe (#ptr-borrow-mut anchor (#ref-ptr anchor))))")
        .replace("#borrow-slice-mut words", "#borrow-slice-mut (#deref writable)")
        .replace("#borrow-slice words", "#borrow-slice (#deref writable)")
        .replace("(#forget words)", "(#forget writable) (#forget anchor)
          (#let released (#ptr-mut (#array #u64 1)) (#unsafe (#pin-release owner)))
          (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (released 8usize))) 0i64))");
    run(&heap);
    let invalid = source.replace("(#let result", "(#set seed 0u64) (#let result");
    let error = compile(&invalid).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn typed_word_reference_slots_use_real_flat_offsets() {
    let source = "(#struct Holder () ((prefix #u128) (value (#ref #u64)) (suffix #u64)))
      (#fn main () #u64
        (#let-mut seed #u64 40u64)
        (#let-mut words (#array #u64 6) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 5usize)
          (#struct-literal Holder ((prefix 0u128) (value (#borrow seed)) (suffix 2u64)))))
        (#let view (#ref Holder) (#unsafe (#word-view (#ref Holder) (#borrow-slice words 1usize 5usize))))
        (#let result #u64 (#u64::add-wrap (#deref (#get view value)) (#get view suffix)))
        (#forget view) (#forget words) (#set seed 0u64) (#return result))";
    run(source);
    let invalid = source.replace(
        "#borrow-slice words 1usize 5usize",
        "#borrow-slice words 0usize 4usize",
    );
    assert!(
        compile(&invalid).is_err(),
        "a neighboring range cannot supply this slot's provenance"
    );
}

#[test]
fn owned_nested_word_slots_preserve_tuple_and_array_reference_origins() {
    let source =
        "(#struct Holder (#linear) ((prefix #u128) (nested (#tuple #u64 (#array (#ref #u64) 2)))))

      (#fn main () #u64
        (#let-mut left #u64 20u64) (#let-mut right #u64 22u64)
        (#let-mut words (#array #u64 5) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((prefix 0u128)
            (nested (#tuple (#tuple #u64 (#array (#ref #u64) 2)) 0u64
              (#array-of (#array (#ref #u64) 2) (#borrow left) (#borrow right))))))))
        (#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let refs (#array (#ref #u64) 2) (#get (#get restored nested) 1))
        (#let answer #u64 (#u64::add-wrap (#deref (#index refs 0usize)) (#deref (#index refs 1usize))))
        (#forget refs) (#forget restored) (#forget words)
        (#set left 0u64) (#set right 0u64) (#return answer))";
    run(source);
    for name in ["left", "right"] {
        let invalid = source.replace("(#let answer", &format!("(#set {name} 0u64) (#let answer"));
        assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
    }
}

#[test]
fn numeric_overwrites_retire_typed_word_reference_provenance() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((value (#borrow seed))))))
        (#unsafe (#word-write #u64 (#borrow-slice-mut words) 0u64))
        (#set seed 42u64) (#return seed))";
    run(source);
    let invalid = source.replace("(#set seed 42u64)",
        "(#let restored Holder (#unsafe (#word-read Holder (#borrow-slice words)))) (#forget restored) (#set seed 42u64)");
    let error = compile(&invalid).unwrap_err();
    assert!(
        error.message.contains("missing slot provenance"),
        "{error:?}"
    );
}

#[test]
fn exclusive_word_reads_require_an_exclusive_source_and_keep_aliases_checked() {
    let source = "(#struct Holder () ((value (#ref-mut #u64))))
      (#fn write ((value (#ref-mut #u64))) () (#deref-set value 42u64) (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((value (#borrow-mut seed))))))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice-mut words))))
        (#call write ((value (#get copied value))))
        (#forget copied) (#forget words) (#return seed))";
    run(source);
    for invalid in [
        source.replace(
            "#word-read Holder (#borrow-slice-mut words)",
            "#word-read Holder (#borrow-slice words)",
        ),
        source.replace(
            "(#call write",
            "(#let alias (#ref #u64) (#borrow seed)) (#call write",
        ),
    ] {
        assert!(
            compile(&invalid).is_err(),
            "exclusive word storage must retain permission and alias checks"
        );
    }
}

#[test]
fn typed_word_writes_cannot_export_short_lived_references() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn bad ((words (#slice-mut #u64))) ()
        (#let local #u64 42u64)
        (#unsafe (#word-write Holder words
          (#struct-literal Holder ((value (#borrow local))))))
        (#return ()))";
    let error = compile(source).expect_err("caller word memory must not retain a local reference");
    assert!(
        matches!(error.code, DiagnosticCode::Borrow | DiagnosticCode::Linear),
        "{error:?}"
    );
}

#[test]
fn typed_word_reference_writes_require_resolved_slot_addresses() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn store ((words (#slice-mut #u64)) (offset #usize) (source (#ref #u64))) ()
        (#unsafe (#word-write Holder (#slice-mut-range words offset 2usize)
          (#struct-literal Holder ((value source)))))
        (#return ()))";
    let error = compile(source).expect_err("unknown coordinates cannot establish typed slots");
    assert!(
        error.message.contains("unresolved slot address"),
        "{error:?}"
    );
}

#[test]
fn typed_word_writer_helpers_export_real_source_loans() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn store ((words (#slice-mut #u64)) (source (#ref #u64))) ()
        (#unsafe (#word-write Holder words (#struct-literal Holder ((value source)))))
        (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#call store ((words (#borrow-slice-mut words)) (source (#borrow seed))))
        (#let copied Holder (#unsafe (#word-read Holder (#borrow-slice words))))
        (#let result #u64 (#deref (#get copied value)))
        (#forget copied) (#forget words) (#set seed 0u64) (#return result))";
    run(source);
    run(&source
        .replace("(#array #u64 1)", "(#array #u64 2)")
        .replace(
            "#borrow-slice-mut words)",
            "#borrow-slice-mut words 1usize 2usize)",
        )
        .replace("#borrow-slice words)", "#borrow-slice words 1usize 2usize)"));
    let invalid = source.replace("(#let result", "(#set seed 0u64) (#let result");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn typed_word_reader_helpers_require_actual_reference_inputs() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#fn read ((words (#slice #u64))) #u64
        (#let restored Holder (#unsafe (#word-read Holder words)))
        (#let answer #u64 (#deref (#get restored value)))
        (#forget restored) (#return answer))
      (#fn forward ((words (#slice #u64))) #u64
        (#return (#call read ((words words)))))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Holder ((value (#borrow seed))))))
        (#let answer #u64 (#call forward ((words (#borrow-slice words 1usize 2usize)))))
        (#forget words) (#set seed 0u64) (#return answer))";
    run(source);
    let invalid = source.replace(
        "(#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)\n          (#struct-literal Holder ((value (#borrow seed))))))", "");
    assert_ne!(source, invalid);
    let error =
        compile(&invalid).expect_err("a scalar return must not hide a forged reference read");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("missing required input loan")
            || error.message.contains("unresolved call inputs"),
        "{error:?}"
    );
}

#[test]
fn moved_by_value_word_backing_retains_caller_validated_loans() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Storage (#linear) ((words (#array #u64 2))))
      (#fn read ((incoming Storage)) #u64
        (#let-mut saved Storage incoming)
        (#let restored Holder (#unsafe (#word-read Holder
          (#borrow-slice (#get saved words) 1usize 2usize))))
        (#let answer #u64 (#deref (#get restored value)))
        (#forget restored) (#forget saved) (#return answer))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Holder ((value (#borrow seed))))))
        (#let storage Storage (#struct-literal Storage ((words words))))
        (#forget words)
        (#let answer #u64 (#call read ((incoming storage))))
        (#set seed 0u64) (#return answer))";
    run(source);
    let field_move = source
        .replace(
            "(#let-mut saved Storage incoming)",
            "(#let-mut extracted (#array #u64 2) (#get incoming words)) (#forget incoming)",
        )
        .replace("(#get saved words)", "extracted")
        .replace("(#forget saved)", "(#forget extracted)");
    run(&field_move);
    let invalid = source.replace(
        "(#unsafe (#word-write Holder (#borrow-slice-mut words 1usize 2usize)\n          (#struct-literal Holder ((value (#borrow seed))))))", "");
    assert_ne!(source, invalid);
    let error =
        compile(&invalid).expect_err("numeric by-value storage must not invent caller loans");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    let wrong_slot = source.replace(
        "#borrow-slice (#get saved words) 1usize 2usize",
        "#borrow-slice (#get saved words) 0usize 1usize",
    );
    assert_eq!(
        compile(&wrong_slot).unwrap_err().code,
        DiagnosticCode::Linear
    );
    let alias = source.replace(
        "(#let answer #u64 (#call read",
        "(#set seed 0u64) (#let answer #u64 (#call read",
    );
    assert_eq!(compile(&alias).unwrap_err().code, DiagnosticCode::Borrow);
}

#[test]
fn moved_exclusive_word_backing_keeps_permissions_and_effects() {
    let source = "(#struct Holder () ((value (#ref-mut #u64))))
      (#struct Storage (#linear) ((words (#array #u64 1))))
      (#fn update ((incoming Storage)) ()
        (#let-mut saved Storage incoming)
        (#let restored Holder (#unsafe (#word-read Holder
          (#borrow-slice-mut (#get saved words)))))
        (#deref-set (#get restored value) 42u64)
        (#forget restored) (#forget saved) (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((value (#borrow-mut seed))))))
        (#let storage Storage (#struct-literal Storage ((words words))))
        (#forget words) (#call update ((incoming storage))) (#return seed))";
    run(source);
    let invalid = source.replace(
        "#borrow-slice-mut (#get saved words)",
        "#borrow-slice (#get saved words)",
    );
    let error = compile(&invalid).unwrap_err();
    assert!(
        matches!(error.code, DiagnosticCode::Linear | DiagnosticCode::Borrow),
        "{error:?}"
    );
    let child = source.replace(
        "(#deref-set (#get restored value) 42u64)",
        "(#let parent (#ref-mut #u64) (#get restored value))
         (#let child (#ref-mut #u64) (#borrow-mut (#deref parent)))
         (#deref-set parent 42u64) (#forget child) (#forget parent)",
    );
    let error = compile(&child).expect_err("an exact handle is still suspended by a live child");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn a_running_thread_retains_by_value_word_input_loans_until_join() {
    let source = "(#struct Holder () ((value (#ref #u64))))
      (#struct Storage (#linear) ((words (#array #u64 1))))
      (#fn read ((incoming Storage)) #u64
        (#let-mut saved Storage incoming)
        (#let restored Holder (#unsafe (#word-read Holder (#borrow-slice (#get saved words)))))
        (#let answer #u64 (#deref (#get restored value)))
        (#forget restored) (#forget saved) (#return answer))
      (#generate #thread-spawn ((task WordTask) (worker read)))
      (#fn main () #u64
        (#let-mut seed #u64 42u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((value (#borrow seed))))))
        (#let storage Storage (#struct-literal Storage ((words words)))) (#forget words)
        (#let answer #u64
          (#match (#call WordTask::spawn ((incoming storage)))
            (#case (WordTask::SpawnResult.Ok handle)
              (#match (#call WordTask::join ((task handle)))
                (#case (WordTask::JoinResult.Ok value) value)
                (#case (WordTask::JoinResult.Error (#tuple retry error)) (#panic))))
            (#case (WordTask::SpawnResult.Error error) (#panic))))
        (#set seed 0u64) (#return answer))";
    run(source);
    let invalid = source
        .replace(
            "(#case (WordTask::SpawnResult.Ok handle)\n              (#match",
            "(#case (WordTask::SpawnResult.Ok handle) (#block (#set seed 0u64)\n              (#match",
        )
        .replace(
            "(#case (WordTask::SpawnResult.Error error)",
            ") (#case (WordTask::SpawnResult.Error error)",
        );
    assert_ne!(source, invalid);
    let error = compile(&invalid).expect_err("running captures must keep the pointee borrowed");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn documented_word_reader_contract_example_runs_natively() {
    let documentation = include_str!("../docs/language.md");
    let section = documentation
        .split("### Typed word-memory loan inputs")
        .nth(1)
        .unwrap();
    let example = section
        .split("```lisp")
        .nth(1)
        .unwrap()
        .split_once('\n')
        .unwrap()
        .1
        .split("```")
        .next()
        .unwrap();
    run(example);
}

#[test]
fn exclusive_word_reader_helpers_cannot_upgrade_shared_permissions() {
    let source = "(#struct Holder () ((value (#ref-mut #u64))))
      (#fn update ((words (#slice-mut #u64))) ()
        (#let restored Holder (#unsafe (#word-read Holder words)))
        (#deref-set (#get restored value) 42u64)
        (#forget restored) (#return ()))
      (#fn main () #u64
        (#let-mut seed #u64 1u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#unsafe (#word-write Holder (#borrow-slice-mut words)
          (#struct-literal Holder ((value (#borrow-mut seed))))))
        (#call update ((words (#borrow-slice-mut words))))
        (#forget words) (#return seed))";
    run(source);
    let invalid = source
        .replace("value (#borrow-mut seed)", "value (#borrow seed)")
        .replace("(#word-write Holder", "(#word-write SharedHolder");
    let invalid = format!("(#struct SharedHolder () ((value (#ref #u64)))) {invalid}").replace(
        "(#struct-literal Holder ((value (#borrow seed))))",
        "(#struct-literal SharedHolder ((value (#borrow seed))))",
    );
    let error = compile(&invalid).expect_err("numeric backing cannot upgrade a shared loan");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn word_reader_contracts_require_permission_on_every_reaching_branch() {
    let source = "(#struct SharedHolder () ((value (#ref #u64))))
      (#struct UniqueHolder () ((value (#ref-mut #u64))))
      (#fn fill ((words (#slice-mut #u64)) (left (#ref-mut #u64)) (right (#ref #u64)) (flag #bool)) ()
        (#if flag
          (#unsafe (#word-write UniqueHolder words (#struct-literal UniqueHolder ((value left)))))
          (#unsafe (#word-write SharedHolder words (#struct-literal SharedHolder ((value right))))))
        (#return ()))
      (#fn update ((words (#slice-mut #u64))) ()
        (#let restored UniqueHolder (#unsafe (#word-read UniqueHolder words)))
        (#deref-set (#get restored value) 42u64) (#forget restored) (#return ()))
      (#fn main () #u64
        (#let-mut left #u64 1u64) (#let right #u64 2u64)
        (#let-mut words (#array #u64 1) (#array-repeat 0u64))
        (#call fill ((words (#borrow-slice-mut words)) (left (#borrow-mut left))
          (right (#borrow right)) (flag true)))
        (#call update ((words (#borrow-slice-mut words))))
        (#forget words) (#return left))";
    let error =
        compile(source).expect_err("a shared alternative must not gain exclusive permission");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn scalar_float_wide_and_pinned_views_use_the_same_word_layout() {
    for (ty, value, read) in [
        ("#i8", "42i8", "(#as (#deref view) #u64)"),
        ("#u128", "42u128", "(#as (#deref view) #u64)"),
        ("#f32", "42.0f32", "(#as (#deref view) #u64)"),
        ("#f64", "42.0f64", "(#as (#deref view) #u64)"),
    ] {
        run(&format!(
            "(#fn main () #u64
          (#let-mut words (#array #u64 2) (#array-repeat 0u64))
          (#unsafe (#word-write {ty} (#borrow-slice-mut words) {value}))
          (#let view (#pin-ref {ty}) (#unsafe (#word-view (#pin-ref {ty}) (#borrow-slice words))))
          (#let result #u64 {read}) (#forget view) (#return result))"
        ));
    }
}

#[test]
fn contiguous_partial_ownership_restoration_keeps_the_whole_address() {
    run("(#struct Token (#linear) ((value #u64)))
      (#struct Owner () ((kept #u64) (item Token)))
      (#fn inspect ((owner (#ref Owner))) #u64
        (#return (#u64::add-wrap (#get owner kept) (#get (#get owner item) value))))
      (#fn main () #u64
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Owner (#borrow-slice-mut words)
          (#struct-literal Owner ((kept 40u64) (item (#struct-literal Token ((value 1u64))))))))
        (#let kept (#ref #u64)
          (#unsafe (#word-view (#ref #u64) (#borrow-slice words 0usize 1usize))))
        (#let moved Token (#unsafe (#word-read Token (#borrow-slice words 1usize 2usize))))
        (#forget moved)
        (#unsafe (#word-write Token (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Token ((value 2u64)))))
        (#let whole (#ref Owner) (#unsafe (#word-view (#ref Owner) (#borrow-slice words))))
        (#let selected (#ref #u64) (#borrow (#get whole kept)))
        (#assert (#usize::eq (#ptr-address (#ref-ptr kept)) (#ptr-address (#ref-ptr selected))))
        (#let answer #u64 (#call inspect ((owner whole))))
        (#forget selected) (#forget whole) (#forget kept)
        (#let remaining Owner (#unsafe (#word-read Owner (#borrow-slice words))))
        (#forget remaining) (#return answer))");
}

#[test]
fn contiguous_reference_owner_restoration_keeps_address_and_real_caller_loan() {
    let source = "(#struct Token (#linear) ((value #u64)))
      (#struct Owner () ((kept (#ref #u64)) (item Token)))
      (#fn inspect ((owner (#ref Owner))) #u64
        (#return (#u64::add-wrap (#deref (#get owner kept)) (#get (#get owner item) value))))
      (#fn main () #u64
        (#let-mut seed #u64 40u64)
        (#let-mut words (#array #u64 2) (#array-repeat 0u64))
        (#unsafe (#word-write Owner (#borrow-slice-mut words)
          (#struct-literal Owner ((kept (#borrow seed)) (item (#struct-literal Token ((value 1u64))))))))
        (#let kept (#ref (#ref #u64))
          (#unsafe (#word-view (#ref (#ref #u64)) (#borrow-slice words 0usize 1usize))))
        (#let moved Token (#unsafe (#word-read Token (#borrow-slice words 1usize 2usize))))
        (#forget moved)
        (#unsafe (#word-write Token (#borrow-slice-mut words 1usize 2usize)
          (#struct-literal Token ((value 2u64)))))
        (#let whole (#ref Owner) (#unsafe (#word-view (#ref Owner) (#borrow-slice words))))
        (#let selected (#ref (#ref #u64)) (#borrow (#get whole kept)))
        (#assert (#usize::eq (#ptr-address (#ref-ptr kept)) (#ptr-address (#ref-ptr selected))))
        (#let answer #u64 (#call inspect ((owner whole))))
        (#forget selected) (#forget whole) (#forget kept) (#forget words)
        (#set seed 0u64) (#return answer))";
    run(source);
    let invalid = source.replace("(#let answer", "(#set seed 0u64) (#let answer");
    assert_eq!(compile(&invalid).unwrap_err().code, DiagnosticCode::Borrow);
}
