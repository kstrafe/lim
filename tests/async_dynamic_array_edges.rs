mod support;

use std::{process::Command, time::Duration};

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

fn run_native(source: &str, label: &str) {
    // Generated async compiler paths can recurse deeply; the CLI stack is
    // separate from Rust's default test-thread stack.
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn_scoped(scope, || run_native_inner(source, label))
            .unwrap()
            .join()
            .unwrap();
    });
}

fn run_native_inner(source: &str, label: &str) {
    let scratch = support::Scratch::new(label);
    let input = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &input,
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    };
    let cold = compile().unwrap_or_else(|error| {
        panic!(
            "{}",
            lim::render_diagnostic(&error, source, &input.display().to_string())
        )
    });
    let warm = compile().unwrap_or_else(|error| panic!("{}", error.message));
    assert_eq!(cold, warm, "cold and warm compilation differ");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &warm,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{status:?} {stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn nested_array_lifetime_anchor_can_read_through_a_shared_pointer_borrow() {
    run_native(
        "#struct Empty () ()
#struct Record () ((header #u64) (tail Empty))
#fn inspect {
  #params = ((data (#pin-ref-mut (#array Record 2))));
  #returns = #u64;
  #body = (
          (#let pointer (#ptr Empty) (#ref-ptr (#pin-borrow (#get (#index data 0usize) tail))))
          (#let view (#ref Empty) (#unsafe (#ptr-borrow
            (#block
              (#let parent (#pin-ref Record) (#pin-borrow (#index data 0usize)))
              (#pin-borrow (#get parent tail))) pointer)))
          (#let value Empty (#deref view)) (#forget value) (#return 42u64)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut data (#array Record 2)
          (#array-of (#array Record 2)
            (#struct-literal Record ((header 1u64) (tail (#struct-literal Empty ()))))
            (#struct-literal Record ((header 2u64) (tail (#struct-literal Empty ()))))))
          (#return (#call inspect ((data (#pin-borrow-mut data)))))\n  );\n}\n",
        "nested-array-lifetime-read",
    );
}

#[test]
fn empty_struct_layout_is_zero_bytes() {
    run_native(
        "#struct Empty () ()\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#return (#if (#usize::eq (#size-of Empty) 0usize) 42u64 43u64))\n  );\n}\n",
        "async-dynamic-empty-layout",
    );
}

#[test]
fn dynamic_empty_array_elements_survive_pending_resume_for_local_and_external_owners() {
    let source = r#"
#struct Empty () ()
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting count)
              (#if (#u64::eq count 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady 1u64)))))
  );
}
#fn cancel-child {
  #params = ((child Child));
  #returns = ();
  #body = ( (#forget child) (#return ())
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (work-cancel ((await-0 cancel-child))))
          (function (#fn work ((choose #bool) (external (#ref (#array Empty 2)))) #u64
            (#let-mut local (#array Empty 2)
              (#array-of (#array Empty 2) (#struct-literal Empty ()) (#struct-literal Empty ())))
            (#let-mut index #usize 0usize)
            (#let selected (#ref Empty)
              (#if choose
                (#borrow (#index local index))
                (#borrow (#index external index))))
            (#set index 1usize)
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#assert (#u64::eq ignored 1u64))
            (#let read-back Empty (#deref selected))
            (#forget read-back)
            (#drop selected) (#forget local)
            (#return 42u64))))
#fn run {
  #params = ((choose #bool));
  #returns = #u64;
  #body = (
          (#let-mut external (#array Empty 2)
            (#array-of (#array Empty 2) (#struct-literal Empty ()) (#struct-literal Empty ())))
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame
            (#call work ((choose choose) (external (#borrow external)))))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll
            ((task pending) (waker (#borrow waker)))))
          (#let answer #u64 (#match second
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending again) (#block (#forget again) (#unreachable)))))
          (#forget task) (#forget external)
          (#return answer)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#assert (#usize::eq (#size-of Empty) 0usize))
          (#assert (#u64::eq (#call run ((choose true))) 42u64))
          (#return (#call run ((choose false))))
  );
}
    "#;
    run_native(source, "async-dynamic-empty-array-edges");
}

#[test]
fn dynamic_nested_trailing_empty_field_survives_pending_resume() {
    run_native(nested_array_source(), "async-dynamic-trailing-empty-edges");
}

#[test]
fn dynamic_nested_nonempty_fields_preserve_shared_and_exclusive_access() {
    for mutable in [false, true] {
        let mut source = nested_array_source()
            .replace("#struct Empty () ()", "")
            .replace("(#assert (#usize::eq (#size-of Empty) 0usize))", "")
            .replace("Empty", "#u64")
            .replace("(#struct-literal #u64 ())", "42u64")
            .replace(
                "(#let-mut index #usize 0usize)",
                "(#let-mut index #usize 1usize)",
            )
            .replace("(#set index 1usize)", "(#set index 0usize)")
            .replace(
                "(#forget read-back)",
                "(#assert (#u64::eq read-back 42u64))",
            );
        if mutable {
            source = source
                .replace("(#ref (#array Record 2))", "(#ref-mut (#array Record 2))")
                .replace(
                    "(#ref #u64)\n              (#if choose",
                    "(#ref-mut #u64)\n              (#if choose",
                )
                .replace("(#borrow (#get (#index", "(#borrow-mut (#get (#index")
                .replace(
                    "external (#borrow external)",
                    "external (#borrow-mut external)",
                )
                .replace(
                    "(#let read-back #u64",
                    "(#deref-set selected 42u64)\n          (#let read-back #u64",
                );
        }
        run_native(&source, "async-dynamic-nested-nonempty");
    }
}

#[test]
fn two_runtime_array_coordinates_preserve_the_selected_leaf() {
    let record = |value| format!("(#struct-literal Record ((header 0u64) (tail {value}u64)))");
    let row = |left, right| format!("(#array-of Row {} {})", record(left), record(right));
    let source = nested_array_source()
        .replace("#struct Empty () ()", "#type Row (#array Record 2)")
        .replace("(#assert (#usize::eq (#size-of Empty) 0usize))", "")
        .replace("Empty", "#u64")
        .replace("(#array Record 2)", "(#array Row 2)")
        // Keep the Row alias's definition nonrecursive.
        .replace(
            "#type Row (#array Row 2)",
            "#type Row (#array Record 2)",
        )
        .replace(
            "(#struct-literal Record ((header 11u64) (tail (#struct-literal #u64 ()))))",
            &row(1, 2),
        )
        .replace(
            "(#struct-literal Record ((header 22u64) (tail (#struct-literal #u64 ()))))",
            &row(3, 42),
        )
        .replace(
            "(#struct-literal Record ((header 31u64) (tail (#struct-literal #u64 ()))))",
            &row(4, 5),
        )
        .replace(
            "(#struct-literal Record ((header 42u64) (tail (#struct-literal #u64 ()))))",
            &row(6, 42),
        )
        .replace(
            "(#let-mut index #usize 0usize)",
            "(#let-mut index #usize 1usize) (#let-mut inner #usize 1usize)",
        )
        .replace(
            "(#index local index)",
            "(#index (#index local index) inner)",
        )
        .replace(
            "(#index external index)",
            "(#index (#index external index) inner)",
        )
        .replace(
            "(#set index 1usize)",
            "(#set index 0usize) (#set inner 0usize)",
        )
        .replace(
            "(#forget read-back)",
            "(#assert (#u64::eq read-back 42u64))",
        );
    assert!(source.contains("(#array-of Row"));
    run_native(&source, "async-two-runtime-array-coordinates");
}

fn nested_array_source() -> &'static str {
    r#"
#struct Empty () ()
#struct Record () ((header #u64) (tail Empty))
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting count)
              (#if (#u64::eq count 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady 1u64)))))
  );
}
#fn cancel-child {
  #params = ((child Child));
  #returns = ();
  #body = ( (#forget child) (#return ())
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (work-cancel ((await-0 cancel-child))))
          (function (#fn work ((choose #bool) (external (#ref (#array Record 2)))) #u64
            (#let-mut local (#array Record 2)
              (#array-of (#array Record 2)
                (#struct-literal Record ((header 11u64) (tail (#struct-literal Empty ()))))
                (#struct-literal Record ((header 22u64) (tail (#struct-literal Empty ()))))))
            (#let-mut index #usize 0usize)
            (#let selected (#ref Empty)
              (#if choose
                (#borrow (#get (#index local index) tail))
                (#borrow (#get (#index external index) tail))))
            (#set index 1usize)
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#assert (#u64::eq ignored 1u64))
            (#let read-back Empty (#deref selected))
            (#forget read-back)
            (#drop selected)
            (#return 42u64))))
#fn run {
  #params = ((choose #bool));
  #returns = #u64;
  #body = (
          (#let-mut external (#array Record 2)
            (#array-of (#array Record 2)
              (#struct-literal Record ((header 31u64) (tail (#struct-literal Empty ()))))
              (#struct-literal Record ((header 42u64) (tail (#struct-literal Empty ()))))))
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame
            (#call work ((choose choose) (external (#borrow external)))))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll
            ((task pending) (waker (#borrow waker)))))
          (#let answer #u64 (#match second
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending again) (#block (#forget again) (#unreachable)))))
          (#forget task) (#forget external)
          (#return answer)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#assert (#usize::eq (#size-of Empty) 0usize))
          (#assert (#u64::eq (#call run ((choose true))) 42u64))
          (#return (#call run ((choose false))))
  );
}
    "#
}
