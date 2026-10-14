mod support;

use std::{fs, process::Command, time::Duration};

fn example_source() -> String {
    include_str!("../examples/pin_rc.lim").replace(
        "../library/pin_rc.lim",
        &format!("{}/library/pin_rc.lim", env!("CARGO_MANIFEST_DIR")),
    )
}

fn replace(source: &str, old: &str, new: &str) -> String {
    assert_eq!(
        source.matches(old).count(),
        1,
        "missing/ambiguous fixture: {old}"
    );
    source.replacen(old, new, 1)
}

fn with_main(source: &str, body: &str) -> String {
    let (prefix, _) = source.rsplit_once("(#fn main ").unwrap();
    format!("{prefix}\n(#fn main () #u64 {body})")
}

fn replace_function(source: &str, name: &str, replacement: &str) -> String {
    let node = lim::parse(source)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#fn")
            && matches!(items.get(1), Some(lim::Expr::Symbol(actual)) if actual == name))
        })
        .unwrap();
    format!(
        "{}{replacement}{}",
        &source[..node.span.start],
        &source[node.span.end..]
    )
}

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("pin-rc-check");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn rejected(source: &str, code: lim::DiagnosticCode, message: &str) {
    let error = compile(source)
        .err()
        .expect("adversarial pin-Rc program must be rejected");
    assert_eq!(error.code, code, "{error:?}");
    assert!(error.message.contains(message), "{error:?}");
    assert!(error.span.is_some(), "{error:?}");
}

fn run(source: &str, label: &str) -> String {
    let scratch = support::Scratch::new(label);
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(30),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(stdout.is_empty());
    let generated = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .map(|entry| {
            let path = entry.unwrap().path();
            assert_eq!(path.extension().unwrap(), "lim");
            let text = fs::read_to_string(path).unwrap();
            assert!(text.starts_with("; Generated from:"));
            lim::parse(&text).expect("inspectable artifacts must be valid ordinary Lim syntax");
            text
        })
        .collect::<Vec<_>>()
        .join("\n");
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
    assert!(stdout.is_empty() && stderr.is_empty());
    generated
}

#[test]
fn clone_refuses_mutation_until_unique_and_destroys_and_deallocates_once() {
    let source = replace(&example_source(),
        "(#let available PinnedNumberRcMutResult",
        "(#assert (#u64.== (#atomic-load (#borrow (#get arena deallocated)) #memory-relaxed) 0u64))\n  (#let available PinnedNumberRcMutResult");
    let generated = run(&source, "pin-rc-native");
    for function in ["create", "clone", "borrow", "borrow-mut", "destroy"] {
        assert!(
            generated.contains(&format!("(#fn PinnedNumberRc-{function}")),
            "{function}"
        );
    }
    for form in [
        "(#pin-shared-own PinnedNumberRcAllocation)",
        "(#pin-share storage)",
        "(#pin-share-clone",
        "(#pin-shared-borrow-mut",
        "(#pin-shared-release pointer)",
        "(#pin-ref #u64)",
        "(#pin-ref-mut #u64)",
    ] {
        assert!(generated.contains(form), "{form}");
    }
}

#[test]
fn pinned_rc_async_resumes_after_moving_the_unique_owner() {
    let source = include_str!("../examples/pinned_rc_async.lim").replace(
        "../library/pin_rc.lim",
        &format!("{}/library/pin_rc.lim", env!("CARGO_MANIFEST_DIR")),
    );
    let generated = run(&source, "pin-rc-async");
    assert!(generated.contains("(#pin-ref-mut Work-frame)"));
    assert!(generated.contains("(#fn work-poll "));
    assert!(generated.contains("(#fn PinnedFrameRc-borrow-mut "));
}

#[test]
fn live_shared_view_blocks_exclusive_access_and_destruction() {
    let source = example_source();
    for operation in [
        "(#let blocked PinnedNumberRcMutResult (#call PinnedNumberRc-borrow-mut (: owner (#borrow-mut moved)))) (#forget blocked)",
        "(#call PinnedNumberRc-destroy (: owner moved))",
    ] {
        let source = if operation == "(#call PinnedNumberRc-destroy (: owner moved))" {
            replace(&source, operation, "")
        } else {
            source.clone()
        };
        let invalid = replace(&source, "(#let answer #u64 (#deref observed))", &format!("{operation}\n  (#let answer #u64 (#deref observed))"));
        rejected(&invalid, lim::DiagnosticCode::Borrow, "borrow");
    }
}

#[test]
fn live_exclusive_view_blocks_shared_access_clone_and_another_exclusive_view() {
    for operation in [
        "(#let blocked (#pin-ref #u64) (#call PinnedNumberRc-borrow (: owner (#borrow moved)))) (#drop blocked)",
        "(#let blocked PinnedNumberRc (#call PinnedNumberRc-clone (: owner (#borrow moved)))) (#call PinnedNumberRc-destroy (: owner blocked))",
        "(#let blocked PinnedNumberRcMutResult (#call PinnedNumberRc-borrow-mut (: owner (#borrow-mut moved)))) (#forget blocked)",
    ] {
        let invalid = replace(&example_source(), "(#unsafe (#pin-write exclusive 42u64))", &format!("{operation}\n  (#unsafe (#pin-write exclusive 42u64))"));
        rejected(&invalid, lim::DiagnosticCode::Borrow, "borrow");
    }
}

#[test]
fn shared_ownership_primitives_require_explicit_unsafe_blocks() {
    for (body, primitive) in [
        ("(#let duplicate (#pin-shared-own #u64) (#pin-share-clone (#borrow owner))) (#forget duplicate) (#forget owner)", "pin-share-clone"),
        ("(#let view (#pin-ref-mut #u64) (#pin-shared-borrow-mut (#borrow-mut owner))) (#drop view) (#forget owner)", "pin-shared-borrow-mut"),
        ("(#let raw (#ptr-mut #u64) (#pin-shared-release owner))", "pin-shared-release"),
    ] {
        let source = format!("(#fn probe (: token (#pin-shared-own #u64)) ()
            (#let-mut owner (#pin-shared-own #u64) token) {body} (#return ()))
            (#fn main () #u64 (#return 42u64))");
        rejected(&source, lim::DiagnosticCode::Unsafe, primitive);
    }
}

#[test]
fn shared_token_is_not_copy_send_sync_or_a_unique_pin_owner() {
    let program = lim::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
    let token = lim::Type::PinShared(Box::new(lim::Type::U64));
    for property in [lim::ThreadProperty::Send, lim::ThreadProperty::Sync] {
        assert!(!lim::type_has_thread_property(&program, &token, property).unwrap());
    }
    let copy = "(#fn duplicate (: token (#pin-shared-own #u64)) ()
      (#let copied (#pin-shared-own #u64) (#clone token)) (#forget copied) (#forget token) (#return ()))
      (#fn main () #u64 (#return 42u64))";
    rejected(copy, lim::DiagnosticCode::Type, "cannot be cloned");
    let release = "(#fn release (: token (#pin-shared-own #u64)) (#ptr-mut #u64)
      (#return (#unsafe (#pin-release token)))) (#fn main () #u64 (#return 42u64))";
    rejected(release, lim::DiagnosticCode::Type, "owning heap pin");
}

fn allocator_source() -> String {
    let source = replace(
        &example_source(),
        "Arena (: destroyed",
        "Arena (: identity #u64 : destroyed",
    );
    let source = replace(
        &source,
        "(: destroyed (#atomic-init",
        "(: identity 0u64 : destroyed (#atomic-init",
    );
    replace(&source, "(#let arena Arena", "(#let-mut arena Arena")
}

const ARENA: &str = "(#let-mut arena Arena (#struct-literal Arena
  (: identity 0u64 : destroyed (#atomic-init #u64 0u64) : deallocated (#atomic-init #u64 0u64))))";
const OWNER: &str = "(#let owner PinnedNumberRc (#match (#call PinnedNumberRc-create (: allocator (#borrow arena) : value 42u64))
  (#case (PinnedNumberRc-created allocated) allocated)
  (#case (PinnedNumberRc-allocation-failed failure) (#block (#forget failure) (#unreachable)))))";

#[test]
fn allocator_is_retained_by_clones_and_direct_or_helper_returned_view_aliases() {
    let base = allocator_source();
    let helper = "(#fn view-alias (: owner (#ref PinnedNumberRc)) (#pin-ref #u64)
      (#return (#call PinnedNumberRc-borrow (: owner owner))))";
    for view in [
        "(#call PinnedNumberRc-borrow (: owner (#borrow clone)))",
        "(#call view-alias (: owner (#borrow clone)))",
    ] {
        let source = with_main(
            &base,
            &format!(
                "{ARENA} {OWNER}
          (#let clone PinnedNumberRc (#call PinnedNumberRc-clone (: owner (#borrow owner))))
          (#forget owner)
          (#let first (#pin-ref #u64) {view})
          (#let retained (#pin-ref #u64) (#clone first)) (#drop first) (#forget clone)
          (#set-field arena identity 99u64)
          (#let answer #u64 (#deref retained)) (#drop retained) (#forget arena) (#return answer)"
            ),
        );
        rejected(
            &format!("{helper}\n{source}"),
            lim::DiagnosticCode::Borrow,
            "arena",
        );
    }
    let source = with_main(
        &base,
        &format!(
            "{ARENA} {OWNER}
      (#let clone PinnedNumberRc (#call PinnedNumberRc-clone (: owner (#borrow owner))))
      (#forget owner) (#set-field arena identity 99u64)
      (#call PinnedNumberRc-destroy (: owner clone)) (#forget arena) (#return 42u64)"
        ),
    );
    rejected(&source, lim::DiagnosticCode::Borrow, "arena");
}

#[test]
fn releasing_views_and_final_owner_allows_allocator_mutation() {
    let source = replace(&allocator_source(), "(#forget arena) (#return answer)",
        "(#set-field arena identity 42u64) (#assert (#u64.== (#get arena identity) answer)) (#forget arena) (#return answer)");
    run(&source, "pin-rc-allocator-release");
}

#[test]
fn rc_handle_cannot_escape_its_allocator() {
    let source = with_main(&allocator_source(), "(#return 42u64)");
    let source = format!(
        "{source}\n(#fn escape () PinnedNumberRc {ARENA} {OWNER} (#forget arena) (#return owner))"
    );
    rejected(
        &source,
        lim::DiagnosticCode::Linear,
        "consumed linear referent",
    );
}

#[test]
fn allocation_failure_returns_the_original_linear_value_without_cleanup() {
    let base = replace(&example_source(), ": type #u64", ": type Value");
    let base = replace_function(
        &base,
        "arena-allocate",
        "(#fn arena-allocate
      (: allocator (#ref Arena) : layout #usize : alignment #usize) AllocationResult
      (#return (AllocationFailed OutOfMemory)))",
    );
    let base = replace_function(&base, "destroy-number", "(#fn destroy-number
      (: allocator (#ref Arena) : pin (#pin-ref-mut Value)) ()
      (#let ignored #u64 (#atomic-fetch-add (#borrow (#get allocator destroyed)) 1u64 #memory-relaxed))
      (#forget pin) (#return ()))");
    let source = with_main(&base, "
      (#let arena Arena (#struct-literal Arena (: destroyed (#atomic-init #u64 0u64) : deallocated (#atomic-init #u64 0u64))))
      (#let result PinnedNumberRcCreateResult (#call PinnedNumberRc-create
        (: allocator (#borrow arena) : value (#struct-literal Value (: amount 42u64)))))
      (#let original Value (#match result
        (#case (PinnedNumberRc-allocation-failed (#tuple error value))
          (#block (#match error (#case OutOfMemory ())) value))
        (#case (PinnedNumberRc-created unexpected) (#block (#call PinnedNumberRc-destroy (: owner unexpected)) (#unreachable)))))
      (#let (Value answer) Value original)
      (#assert (#u64.== (#atomic-load (#borrow (#get arena destroyed)) #memory-relaxed) 0u64))
      (#assert (#u64.== (#atomic-load (#borrow (#get arena deallocated)) #memory-relaxed) 0u64))
      (#forget arena) (#return answer)");
    run(
        &format!("(#struct Value (: amount #u64)) (#linear Value)\n{source}"),
        "pin-rc-allocation-failure",
    );
}

fn nested_reference_source(body: &str) -> String {
    let base = replace(&allocator_source(), ": type #u64", ": type Value");
    let base = replace_function(&base, "destroy-number", "(#fn destroy-number
      (: allocator (#ref Arena) : pin (#pin-ref-mut Value)) ()
      (#assert (#u64.== (#deref (#get pin reference)) 42u64))
      (#let ignored #u64 (#atomic-fetch-add (#borrow (#get allocator destroyed)) 1u64 #memory-relaxed))
      (#forget pin) (#return ()))");
    let source = with_main(&base, body);
    format!(
        "(#struct Value (: reference (#ref #u64))) (#linear Value)
      (#fn nested-view (: owner (#ref PinnedNumberRc)) (#pin-ref Value)
        (#return (#call PinnedNumberRc-borrow (: owner owner))))\n{source}"
    )
}

fn nested_reference_body(tail: &str) -> String {
    let owner = replace(
        OWNER,
        ": value 42u64",
        ": value (#struct-literal Value (: reference (#borrow source)))",
    );
    format!(
        "{ARENA} (#let-mut source #u64 42u64) {owner}
      (#let clone PinnedNumberRc (#call PinnedNumberRc-clone (: owner (#borrow owner))))
      (#forget owner) {tail}"
    )
}

#[test]
fn cloned_handle_retains_references_nested_in_the_pinned_value() {
    let tail =
        "(#let view (#pin-ref Value) (#call PinnedNumberRc-borrow (: owner (#borrow clone))))
      (#let answer #u64 (#deref (#get view reference))) (#drop view)
      (#call PinnedNumberRc-destroy (: owner clone))
      (#assert (#u64.== (#atomic-load (#borrow (#get arena destroyed)) #memory-relaxed) 0u64))
      (#forget arena) (#return answer)";
    // The original owner was leaked, so destroying the clone must not destroy
    // the still-shared allocation. Its nested reference nevertheless stays live.
    run(
        &nested_reference_source(&nested_reference_body(tail)),
        "pin-rc-nested-reference",
    );
    let invalid = nested_reference_body(&format!("(#set source 99u64) {tail}"));
    rejected(
        &nested_reference_source(&invalid),
        lim::DiagnosticCode::Borrow,
        "source",
    );
}

#[test]
fn direct_and_helper_returned_views_retain_nested_references_after_handles_are_forgotten() {
    for view in [
        "(#call PinnedNumberRc-borrow (: owner (#borrow clone)))",
        "(#call nested-view (: owner (#borrow clone)))",
    ] {
        let tail = format!(
            "(#let view (#pin-ref Value) {view}) (#forget clone)
          (#let answer #u64 (#deref (#get view reference))) (#drop view)
          (#forget arena) (#return answer)"
        );
        compile(&nested_reference_source(&nested_reference_body(&tail)))
            .unwrap_or_else(|error| panic!("valid nested-view fixture: {error:?}"));
        let invalid = replace(
            &tail,
            "(#let answer #u64",
            "(#set source 99u64) (#let answer #u64",
        );
        rejected(
            &nested_reference_source(&nested_reference_body(&invalid)),
            lim::DiagnosticCode::Borrow,
            "source",
        );
    }
}

#[test]
fn cloning_ownership_retains_exclusive_reference_contents_without_lending_them() {
    let tail =
        "(#let view (#pin-ref Value) (#call PinnedNumberRc-borrow (: owner (#borrow clone))))
      (#let answer #u64 (#deref (#get view reference))) (#drop view)
      (#call PinnedNumberRc-destroy (: owner clone))
      (#forget arena) (#return answer)";
    let source = nested_reference_source(&nested_reference_body(tail))
        .replace(
            "Value (: reference (#ref #u64))",
            "Value (: reference (#ref-mut #u64))",
        )
        .replace(
            ": reference (#borrow source)",
            ": reference (#borrow-mut source)",
        );
    run(&source, "pin-rc-exclusive-contents");
    let invalid = replace(
        &source,
        "(#let answer #u64",
        "(#set source 99u64) (#let answer #u64",
    );
    rejected(&invalid, lim::DiagnosticCode::Borrow, "source");
}
