use std::{process::Command, time::Duration};
mod support;

fn prefix() -> String {
    format!(
        r#"(#import "{}/library/pin.lim")
      (#struct Inner (#linear) (: value #u64))
      (#struct Outer (#linear) (: left Inner : right Inner))
      (@#pin (: type Inner : name PinnedInner : fields (: value #u64)))
      (@#pin (: type Outer : name PinnedOuter : projections (: left PinnedInner : right PinnedInner)))
      (@#pin-scope (: type Outer : pin PinnedOuter : name with-outer
        : run drive : destroy destroy : result #u64))
      (#fn destroy (: pin PinnedOuter) () (#forget pin) (#return ()))
      (#fn main () #u64 (#return (#call with-outer
        (: value (#struct-literal Outer
          (: left (#struct-literal Inner (: value 0u64))
           : right (#struct-literal Inner (: value 0u64))))))))"#,
        env!("CARGO_MANIFEST_DIR")
    )
}

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("pin-projection-borrow");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str) {
    let assembly = compile(source).unwrap_or_else(|e| panic!("{}", e.message));
    let scratch = support::Scratch::new("pin-projection-native");
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
    assert!(stdout.is_empty() && stderr.is_empty());
}

const DRIVE: &str = r#"(#fn drive (: pin PinnedOuter) #u64
  (#let-mut parent PinnedOuter pin)
  (#let-mut left PinnedInner (#call PinnedOuter::left::borrow-mut (: pin (#borrow-mut parent))))
  (#let-mut right PinnedInner (#call PinnedOuter::right::borrow-mut (: pin (#borrow-mut parent))))
  (#call PinnedInner::value::write (: pin (#borrow-mut left) : value 20u64))
  (#call PinnedInner::value::write (: pin (#borrow-mut right) : value 22u64))
  (#let answer #u64 (#u64.+.wrap
    (#call PinnedInner::value::read (: pin (#borrow left)))
    (#call PinnedInner::value::read (: pin (#borrow right)))))
  (#forget left) (#forget right) (#forget parent) (#return answer))"#;

#[test]
fn disjoint_child_projections_keep_the_parent_handle() {
    run(&format!("{} {DRIVE}", prefix()));
}

#[test]
fn overlapping_child_projections_reject_at_the_second_call() {
    let source = format!(
        "{} {}",
        prefix(),
        DRIVE.replace(
            "PinnedOuter::right::borrow-mut",
            "PinnedOuter::left::borrow-mut"
        )
    );
    let error = compile(&source)
        .err()
        .expect("the same field cannot be borrowed exclusively twice");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    let span = error.span.expect("second call argument must be underlined");
    assert_eq!(&source[span.start..span.end], "(#borrow-mut parent)");
    assert!(error
        .labels
        .iter()
        .any(|label| label.message.contains("callee")));
}

#[test]
fn forgetting_a_wrapper_does_not_destroy_its_stationary_referent() {
    let source = format!(
        "{} {}",
        prefix(),
        DRIVE
            .replace(
                "(#call PinnedInner::value::write (: pin (#borrow-mut left)",
                "(#forget parent) (#call PinnedInner::value::write (: pin (#borrow-mut left)"
            )
            .replace("(#forget right) (#forget parent)", "(#forget right)")
    );
    run(&source);
}

#[test]
fn shared_projections_coexist_but_prevent_an_exclusive_projection() {
    let drive = r#"(#fn drive (: pin PinnedOuter) #u64
      (#let-mut parent PinnedOuter pin)
      (#let-mut initial PinnedInner (#call PinnedOuter::left::borrow-mut (: pin (#borrow-mut parent))))
      (#call PinnedInner::value::write (: pin (#borrow-mut initial) : value 42u64))
      (#forget initial)
      (#let first PinnedInner::shared (#call PinnedOuter::left::borrow (: pin (#borrow parent))))
      (#let second PinnedInner::shared (#call PinnedOuter::left::borrow (: pin (#borrow parent))))
      (#let answer #u64 (#call PinnedInner::shared::value::read (: pin (#borrow first))))
      (#assert (#u64.== (#call PinnedInner::shared::value::read (: pin (#borrow second))) answer))
      (#forget first) (#forget second) (#forget parent) (#return answer))"#;
    run(&format!("{} {drive}", prefix()));
    let bad = drive.replace("(#let answer #u64", "(#let exclusive PinnedInner (#call PinnedOuter::left::borrow-mut (: pin (#borrow-mut parent)))) (#forget exclusive) (#let answer #u64");
    let error = compile(&format!("{} {bad}", prefix()))
        .err()
        .expect("shared children block overlapping exclusive access");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn consuming_a_parent_for_projection_does_not_bypass_a_retained_child() {
    let bad = DRIVE
        .replace(
            "PinnedOuter::right::borrow-mut (: pin (#borrow-mut parent))",
            "PinnedOuter::left::project-mut (: pin parent)",
        )
        .replace("(#forget right) (#forget parent)", "(#forget right)");
    let error = compile(&format!("{} {bad}", prefix()))
        .err()
        .expect("consuming a wrapper cannot duplicate its pointee permission");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn helper_accesses_are_checked_even_when_the_child_is_transferred_to_the_call() {
    let helper = r#"(#fn helper (: parent (#ref-mut PinnedOuter) : child PinnedInner) ()
      (#let-mut sibling PinnedInner (#call PinnedOuter::left::borrow-mut (: pin parent)))
      (#call PinnedInner::value::write (: pin (#borrow-mut sibling) : value 99u64))
      (#forget sibling)
      (#let-mut held PinnedInner child)
      (#call PinnedInner::value::write (: pin (#borrow-mut held) : value 20u64))
      (#forget held) (#return ()))"#;
    let drive = r#"(#fn drive (: pin PinnedOuter) #u64
      (#let-mut parent PinnedOuter pin)
      (#let left PinnedInner (#call PinnedOuter::left::borrow-mut (: pin (#borrow-mut parent))))
      (#call helper (: parent (#borrow-mut parent) : child left))
      (#forget parent) (#return 42u64))"#;
    let source = format!("{} {helper} {drive}", prefix());
    let error = compile(&source)
        .err()
        .expect("the transferred child's loan remains active during the helper call");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("another argument"),
        "{}",
        error.message
    );
    let disjoint = source.replace(
        "PinnedOuter::left::borrow-mut (: pin parent)",
        "PinnedOuter::right::borrow-mut (: pin parent)",
    );
    run(&disjoint);
}

#[test]
fn void_helpers_cannot_touch_a_retained_exclusive_child() {
    let helper = r#"(#fn touch (: parent (#ref-mut PinnedOuter)) ()
      (#let-mut temporary PinnedInner (#call PinnedOuter::left::borrow-mut (: pin parent)))
      (#call PinnedInner::value::write (: pin (#borrow-mut temporary) : value 99u64))
      (#forget temporary) (#return ()))"#;
    let bad = DRIVE.replace(
        "(#let-mut right PinnedInner",
        "(#call touch (: parent (#borrow-mut parent))) (#let-mut right PinnedInner",
    );
    let error = compile(&format!("{} {helper} {bad}", prefix()))
        .err()
        .expect("a helper's return type cannot conceal a pointee access");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn heap_child_views_prevent_release_and_disjoint_borrows_still_work() {
    let prefix = prefix();
    let declarations = prefix.split("(@#pin-scope").next().unwrap();
    let source = format!(
        r#"{declarations}
      (#fn destroy-heap (: owner (#pin-own Outer)) ()
        (#let pointer (#ptr-mut Outer) (#unsafe (#pin-release owner)))
        (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))
        (#return ()))
      (#fn main () #u64
        (#let pointer (#ptr-mut Outer) (#unsafe (#linux-syscall (#ptr-mut Outer) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let-mut owner (#pin-own Outer) (#unsafe (#pin-own-of pointer
          (#struct-literal Outer (: left (#struct-literal Inner (: value 0u64))
            : right (#struct-literal Inner (: value 0u64)))))))
        (#let-mut parent PinnedOuter (#unsafe (#call PinnedOuter::from-mut
          (: view (#pin-own-borrow-mut owner)))))
        (#let-mut left PinnedInner (#call PinnedOuter::left::borrow-mut (: pin (#borrow-mut parent))))
        (#let-mut right PinnedInner (#call PinnedOuter::right::borrow-mut (: pin (#borrow-mut parent))))
        (#call PinnedInner::value::write (: pin (#borrow-mut left) : value 20u64))
        (#call PinnedInner::value::write (: pin (#borrow-mut right) : value 22u64))
        (#let answer #u64 (#u64.+.wrap (#call PinnedInner::value::read (: pin (#borrow left)))
          (#call PinnedInner::value::read (: pin (#borrow right)))))
        (#forget left) (#forget right) (#forget parent)
        (#call destroy-heap (: owner owner)) (#return answer))"#
    );
    run(&source);
    let bad = source
        .replace(
            "(#let answer #u64",
            "(#forget parent) (#call destroy-heap (: owner owner)) (#let answer #u64",
        )
        .replace(
            "(#forget left) (#forget right) (#forget parent)",
            "(#forget left) (#forget right)",
        )
        .replace(
            "(#call destroy-heap (: owner owner)) (#return answer)",
            "(#return answer)",
        );
    let error = compile(&bad)
        .err()
        .expect("actual heap allocation must outlive its child handles");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("pinned allocation"),
        "{}",
        error.message
    );
}
