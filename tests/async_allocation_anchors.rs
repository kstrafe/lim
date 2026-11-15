mod support;

use std::{process::Command, time::Duration};

fn ordinary_generated_source(source: &str) -> String {
    let mut body = source.to_owned();
    for form in lim::parse_source_unit(source).unwrap().into_iter().rev() {
        if matches!(&form.expr, lim::Expr::List(items) if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#generated-context"))
        {
            body.replace_range(form.span.start..form.span.end, "");
        }
    }
    body
}

const PREFIX: &str = r#"
#struct Data () ((padding #u128) (value #u64) (sentinel #u64))
#static fallback-storage Data (#struct-literal Data ((padding 999u128) (value 60u64) (sentinel 70u64)))
#static destroyed (#atomic #u64) (#atomic-init #u64 0u64)
#static cancelled (#atomic #u64) (#atomic-init #u64 0u64)
#fn make-heap () (#pin-own Data)
    (#let pointer (#ptr-mut Data) (#unsafe (#linux-syscall (#ptr-mut Data) 9usize
      (0usize 4096usize 3usize 34usize -1i64 0usize))))
    (#assert (#usize::lt (#ptr-address pointer) 18446744073709547520usize))
    (#return (#unsafe (#pin-own-of pointer
      (#struct-literal Data ((padding 123u128) (value 50u64) (sentinel 80u64))))))
#fn destroy-heap ((owner (#pin-own Data))) ()
    (#let view (#pin-ref Data) (#pin-own-borrow owner))
    (#assert (#u64::eq (#get view sentinel) 80u64))
    (#drop view)
    (#let pointer (#ptr-mut Data) (#unsafe (#pin-release owner)))
    (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))
    (#let ignored #u64 (#unsafe (#atomic-fetch-add (#borrow destroyed) 1u64 #memory-relaxed)))
    (#return ())
#enum Child (#linear) ((Child.Holding (#tuple (#pin-ref #u64) #u64)))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
    (#return (#match task (#case (Child.Holding (#tuple reference count))
      (#if (#u64::lt count 2u64)
        (ChildPoll.ChildPending (Child.Holding (#tuple reference (#u64::add-wrap count 1u64))))
        (ChildPoll.ChildReady (#deref reference))))))
#fn cancel-child ((child Child)) ()
    (#match child (#case (Child.Holding (#tuple reference count)) (#block
      (#assert (#u64::ge (#deref reference) 40u64))
      (#drop reference) ())))
    (#let ignored #u64 (#unsafe (#atomic-fetch-add (#borrow cancelled) 1u64 #memory-relaxed)))
    (#return ())
#fn verify-cancel ((phase #u64)) ()
    (#let expected #u64 (#if (#bool::or (#u64::eq phase 1u64) (#u64::eq phase 2u64)) 1u64 0u64))
    (#assert (#u64::eq (#unsafe (#atomic-load (#borrow cancelled) #memory-relaxed)) expected))
    (#return ())
"#;

fn direct_source() -> String {
    format!(
        r#"{PREFIX}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
    (cancel (work-cancel ((heap destroy-heap) (await-0 cancel-child))))
    (function (#fn work ((choice #u64)) #u64
      (#let-mut local (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) 90u64 40u64))
      (#let-mut heap (#pin-own Data) (#call make-heap ()))
      (#let view (#pin-ref #u64)
        (#if (#u64::eq choice 0u64) (#pin-borrow (#get local 1))
          (#if (#u64::eq choice 1u64)
            (#block (#let allocation (#pin-ref Data) (#pin-own-borrow heap))
              (#pin-borrow (#get allocation value)))
            (#unsafe (#pin-borrow (#get fallback-storage value))))))
      (#let answer #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Holding (#tuple view 0u64))))
      (#drop view)
      (#call destroy-heap ((owner heap)))
      (#forget local)
      (#return answer))))
#fn run ((choice #u64) (cancel-at #u64)) #u64
    (#unsafe (#atomic-store (#borrow destroyed) 0u64 #memory-relaxed))
    (#let waker #u64 0u64)
    (#let-mut frame Work::Frame (#call work (($ choice))))
    (#if (#u64::eq cancel-at 0u64) (#block
      (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
      (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
      (#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 0u64))
      (#forget frame) (#return 42u64)) ())
    (#let-mut polls #u64 0u64)
    (#let answer #u64 (#loop
      (#let result Work::Poll (#call Work::poll
        ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
      (#set polls (#u64::add-wrap polls 1u64))
      (#match result
        (#case (Work::Poll.Pending pending) (#block
          (#drop pending)
          (#if (#u64::eq polls cancel-at) (#block
            (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
            (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
            (#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 1u64))
            (#forget frame) (#return 42u64)) ())
          (#continue)))
        (#case (Work::Poll.Ready value) (#block (#break value))))))
    (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
    (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
    (#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 1u64))
    (#assert (#u64::eq answer (#u64::add-wrap 40u64 (#u64::mul-wrap choice 10u64))))
    (#forget frame) (#return 42u64)
#fn main () #u64
    (#assert (#u64::eq (#call run ((choice 0u64) (cancel-at 9u64))) 42u64))
    (#assert (#u64::eq (#call run ((choice 1u64) (cancel-at 9u64))) 42u64))
    (#assert (#u64::eq (#call run ((choice 2u64) (cancel-at 9u64))) 42u64))
    (#assert (#u64::eq (#call run ((choice 0u64) (cancel-at 0u64))) 42u64))
    (#assert (#u64::eq (#call run ((choice 1u64) (cancel-at 1u64))) 42u64))
    (#assert (#u64::eq (#call run ((choice 2u64) (cancel-at 2u64))) 42u64))
    (#return 42u64)
"#
    )
}

fn source() -> String {
    let source = direct_source()
        .replace("((heap destroy-heap) (await-0 cancel-child))", "((await-0 cancel-child))")
        .replace("(#fn work ((choice #u64))", "(#fn work ((choice #u64) (allocated (#pin-ref #u64)) (fallback (#pin-ref #u64)))")
        .replace("      (#let-mut heap (#pin-own Data) (#call make-heap ()))\n", "")
        .replace("(#block (#let allocation (#pin-ref Data) (#pin-own-borrow heap))\n              (#pin-borrow (#get allocation value)))", "allocated")
        .replace("(#unsafe (#pin-borrow (#get fallback-storage value)))", "fallback")
        .replace("      (#call destroy-heap ((owner heap)))\n", "")
        .replace("  (#let-mut frame Work::Frame (#call work (($ choice))))", "  (#let heap (#pin-own Data) (#call make-heap ()))\n  (#let allocation (#pin-ref Data) (#pin-own-borrow heap))\n  (#let-mut frame Work::Frame (#call work ((choice choice) (allocated (#pin-borrow (#get allocation value))) (fallback (#unsafe (#pin-borrow (#get fallback-storage value)))))))")
        .replace("(#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 1u64))", "(#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 0u64))")
        .replace("(#forget frame)", "(#forget frame) (#drop allocation) (#call destroy-heap ((owner heap)))\n    (#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 1u64))");
    let start = source.find("  (#let-mut polls").unwrap();
    let end = source.find("  (#assert (#u64::eq answer").unwrap();
    let driver = r#"
  (#let first Work::Poll (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
  (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
  (#if (#u64::eq cancel-at 1u64) (#block
    (#call Work::Poll::destroy ((task pending)))
    (#drop pending)
    (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
    (#forget frame) (#drop allocation) (#call destroy-heap ((owner heap)))
    (#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 1u64))
    (#return 42u64)) ())
  (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
  (#drop pending)
  (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))
  (#if (#u64::eq cancel-at 2u64) (#block
    (#call Work::Poll::destroy ((task last)))
    (#drop last)
    (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
    (#forget frame) (#drop allocation) (#call destroy-heap ((owner heap)))
    (#assert (#u64::eq (#unsafe (#atomic-load (#borrow destroyed) #memory-relaxed)) 1u64))
    (#return 42u64)) ())
  (#let third Work::Poll (#call Work::poll ((task last) (waker (#borrow waker)))))
  (#drop last)
  (#let answer #u64 (#match third
    (#case (Work::Poll.Ready value) value)
    (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
  (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
"#;
    let source = format!("{}{driver}{}", &source[..start], &source[end..])
        .replace("(#forget frame)", "(#forget frame) (#call verify-cancel ((phase cancel-at)))")
        .replace("  (#let waker #u64 0u64)", "  (#unsafe (#atomic-store (#borrow cancelled) 0u64 #memory-relaxed))\n  (#let waker #u64 0u64)");
    let main = source.rfind("#fn main ").unwrap();
    let mut source = source[..main].to_owned();
    source.push_str("#fn main () #u64\n");
    for choice in 0..3 {
        for cancel in [0, 1, 2, 9] {
            source.push_str(&format!("  (#assert (#u64::eq (#call run ((choice {choice}u64) (cancel-at {cancel}u64))) 42u64))\n"));
        }
    }
    source.push_str("  (#return 42u64)");
    source
}

fn compile(source: &str, scratch: &support::Scratch) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str) {
    let scratch = support::Scratch::new("async-allocation-anchors");
    let cold = compile(source, &scratch).unwrap_or_else(|error| {
        panic!(
            "{}\n{source}",
            lim::render_diagnostic(&error, source, "main.lim")
        )
    });
    let warm = compile(source, &scratch).unwrap();
    assert_eq!(cold, warm);
    for (name, assembly) in [("cold", cold), ("warm", warm)] {
        let binary = scratch.path().join(name);
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
        assert!(stdout.is_empty() && stderr.is_empty());
    }
}

#[test]
fn mixed_local_allocation_static_targets_survive_pending_and_cancel_in_order() {
    run(&source());
}

#[test]
fn direct_ordinary_allocation_mix_requires_a_real_owner_recipe() {
    // No executor driver or dependent child is needed to exercise the planner.
    let source = "#struct Data (#linear) ((value #u64))
#fn make () (#pin-own Data)
          (#let pointer (#ptr-mut Data) (#unsafe (#linux-syscall (#ptr-mut Data) 9usize (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#return (#unsafe (#pin-own-of pointer (#struct-literal Data ((value 42u64))))))
#fn destroy ((owner (#pin-own Data))) ()
          (#let pointer (#ptr-mut Data) (#unsafe (#pin-release owner)))
          (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) (#return ())
#enum Child (#linear) ((Child.Waiting #u64))
#enum Poll () ((Poll.Pending Child) (Poll.Ready #u64))
#fn poll ((task Child) (waker (#ref #u64))) Poll
          (#return (#match task (#case (Child.Waiting value) (#enum-literal Poll.Ready value))))
#fn cancel ((task Child)) () (#forget task) (#return ())
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64) (cancel (work-cancel ((heap destroy) (await-0 cancel))))
          (function (#fn work ((choose #bool)) #u64
            (#let-mut local #u64 40u64) (#let-mut heap (#pin-own Data) (#call make ()))
            (#let view (#ref #u64) (#if choose (#borrow local) (#block
              (#let anchor (#pin-ref Data) (#pin-own-borrow heap))
              (#unsafe (#ptr-borrow anchor (#ref-ptr (#pin-borrow (#get anchor value))))))))
            (#let ignored #u64 (#await Child Poll.Pending Poll.Ready poll (#enum-literal Child.Waiting 0u64)))
            (#let answer #u64 (#deref view)) (#drop view) (#call destroy ((owner heap))) (#forget local) (#return answer))))
#fn main () #u64 (#return 0u64)\n";
    let scratch = support::Scratch::new("async-direct-allocation-owner-recipe");
    let diagnostic =
        compile(source, &scratch).expect_err("unrepresented owning allocation must fail closed");
    assert!(
        matches!(
            diagnostic.code,
            lim::DiagnosticCode::Linear | lim::DiagnosticCode::Type
        ),
        "{}",
        diagnostic.message
    );
    assert!(
        diagnostic.message.contains("retained owner recipe")
            || diagnostic.message.contains("missing slot provenance"),
        "{}",
        diagnostic.message
    );
    assert!(
        diagnostic.span.is_some(),
        "unsupported recipe needs a source span"
    );
}

#[test]
fn mixed_local_allocation_exclusive_targets_survive_pending_and_cancellation() {
    let source = source()
        .replace("(#pin-ref #u64)", "(#pin-ref-mut #u64)")
        .replace(" (fallback (#pin-ref-mut #u64))", "")
        .replace(" (fallback (#unsafe (#pin-borrow (#get fallback-storage value))))", "")
        .replace("(#if (#u64::eq choice 1u64)\n            allocated\n            fallback)", "allocated")
        .replace("(#let heap (#pin-own Data)", "(#let-mut heap (#pin-own Data)")
        .replace("(#pin-ref Data) (#pin-own-borrow heap)", "(#pin-ref-mut Data) (#pin-own-borrow-mut (#borrow-mut heap))")
        .replace("(#pin-borrow (#get local 1))", "(#pin-borrow-mut (#get local 1))")
        .replace("(#pin-borrow (#get allocation value))", "(#pin-borrow-mut (#get allocation value))")
        .replace("      (#drop view)\n", "")
        .replace("(ChildPoll.ChildReady (#deref reference))", "(#block (#unsafe (#pin-write reference (#u64::add-wrap (#deref reference) 1u64))) (ChildPoll.ChildReady (#deref reference)))")
        .replace("(#u64::add-wrap 40u64 (#u64::mul-wrap choice 10u64))", "(#u64::add-wrap 41u64 (#u64::mul-wrap choice 10u64))");
    let source = source
        .lines()
        .filter(|line| !line.contains("(#call run ((choice 2u64"))
        .collect::<Vec<_>>()
        .join("\n");
    run(&source);
}

#[test]
fn immutable_static_does_not_gain_exclusive_pinning_permission() {
    let source = format!("{PREFIX}\n#fn invalid () (#pin-ref-mut #u64)\n    (#return (#unsafe (#pin-borrow-mut (#get fallback-storage value))))\n");
    let scratch = support::Scratch::new("async-static-exclusive-rejection");
    let error = compile(&source, &scratch).expect_err("static is immutable even inside unsafe");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("immutable"), "{error:?}");
    assert!(error.span.is_some());
}

#[test]
fn selected_allocation_cannot_be_released_before_the_suspended_borrow() {
    let source = source()
        .replace("(#call destroy-heap ((owner heap)))", "")
        .replace(
            "  (#if (#u64::eq cancel-at 0u64)",
            "  (#call destroy-heap ((owner heap)))\n  (#if (#u64::eq cancel-at 0u64)",
        );
    let scratch = support::Scratch::new("async-selected-allocation-release");
    for _ in 0..2 {
        let error = compile(&source, &scratch).expect_err("selected allocation remains borrowed");
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        let span = error.span.expect("source-spanned borrow error");
        assert!(
            source[span.start..span.end].contains("destroy-heap"),
            "{error:?}"
        );
    }
}

#[test]
fn shared_selected_allocation_does_not_grant_exclusive_access() {
    let source = source().replace("(#let heap (#pin-own Data)", "(#let-mut heap (#pin-own Data)")
        .replace("  (#let first", "  (#let conflicting (#pin-ref-mut Data) (#pin-own-borrow-mut (#borrow-mut heap)))\n  (#drop conflicting)\n  (#let first");
    let scratch = support::Scratch::new("async-selected-allocation-alias");
    let error =
        compile(&source, &scratch).expect_err("shared selected loan prevents exclusive borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert!(
        source[span.start..span.end].contains("borrow-mut"),
        "{error:?}"
    );
}

#[test]
fn mixed_allocation_static_artifacts_are_independently_checked_ordinary_lim() {
    let source = source();
    let scratch = support::Scratch::new("async-allocation-independent");
    let generated = scratch.path().join("generated");
    lim::write_generated_sources_from_path_with_config_and_cache(
        &source,
        &scratch.path().join("main.lim"),
        &generated,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
    )
    .unwrap();
    let mut standalone = source.clone();
    for form in lim::parse_source_unit(&source).unwrap().into_iter().rev() {
        if source[form.span.start..form.span.end].starts_with("#generate ") {
            standalone.replace_range(form.span.start..form.span.end, "");
        }
    }
    for entry in std::fs::read_dir(generated).unwrap() {
        let text = std::fs::read_to_string(entry.unwrap().path()).unwrap();
        assert!(!text.contains("#await"));
        standalone.push('\n');
        standalone.push_str(&ordinary_generated_source(&text));
    }
    let program = lim::parse_program(&standalone).unwrap();
    lim::check_types(&program).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("standalone");
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
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn direct_static_field_borrow_keeps_global_identity_across_pending() {
    let source = format!(
        r#"{PREFIX}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
    (cancel (work-cancel ((await-0 cancel-child))))
    (function (#fn work () #u64
      (#let view (#pin-ref #u64) (#unsafe (#pin-borrow (#get fallback-storage value))))
      (#let answer #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Holding (#tuple view 0u64))))
      (#drop view) (#return answer))))
#fn main () #u64
    (#let waker #u64 0u64)
    (#let-mut frame Work::Frame (#call work ()))
    (#let first Work::Poll (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
    (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
    (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
    (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))
    (#let third Work::Poll (#call Work::poll ((task last) (waker (#borrow waker)))))
    (#let answer #u64 (#match third (#case (Work::Poll.Ready value) value)
      (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
    (#call Work::Poll::destroy ((task (#pin-borrow-mut frame))))
    (#forget frame) (#assert (#u64::eq answer 60u64)) (#return 42u64)
"#
    );
    run(&source);
    run(&source.replace("#static fallback-storage Data (#struct-literal Data ((padding 999u128) (value 60u64) (sentinel 70u64)))",
        "#static fallback-storage (#tuple #u8 #u64) (#tuple (#tuple #u8 #u64) 1u8 60u64)")
        .replace("(#get fallback-storage value)", "(#get fallback-storage 1)"));
    let invalid = source.replace(
        "(#unsafe (#pin-borrow (#get fallback-storage value)))",
        "(#pin-borrow (#get fallback-storage value))",
    );
    let scratch = support::Scratch::new("async-direct-static-unsafe");
    let error = compile(&invalid, &scratch).expect_err("source static access must remain unsafe");
    assert_eq!(error.code, lim::DiagnosticCode::Unsafe, "{error:?}");
}
