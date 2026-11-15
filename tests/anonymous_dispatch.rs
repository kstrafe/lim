mod support;

use std::{fs, path::Path, process::Command, time::Duration};

fn compile(
    source: &str,
    root: &Path,
) -> Result<(String, Vec<lim::DispatchManifest>), lim::Diagnostic> {
    let (assembly, manifests) = lim::with_dispatch_manifest(|| {
        lim::compile_source_to_assembly(
            source,
            &root.join("main.lim"),
            &lim::CompileConfig::default(),
            &root.join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    });
    assembly.map(|assembly| (assembly, manifests))
}

fn run_fresh_and_cached(source: &str, root: &Path) -> Vec<lim::DispatchManifest> {
    run_cached_result(source, root, true)
}

fn run_cached_result(source: &str, root: &Path, has_fields: bool) -> Vec<lim::DispatchManifest> {
    fs::write(root.join("main.lim"), source).unwrap();
    let mut previous = None;
    let mut last = Vec::new();
    for pass in 0..2 {
        let (assembly, manifests) = compile(source, root).unwrap();
        assert_eq!(manifests.len(), 1);
        let artifact = fs::read_to_string(&manifests[0].generated_path).unwrap();
        if has_fields {
            assert!(artifact.contains("#let"), "{artifact}");
            assert!(artifact.contains("#record-literal"), "{artifact}");
        } else {
            assert!(artifact.contains("#returns = ();"), "{artifact}");
        }
        assert!(!artifact.contains("lim.gensym.record."), "{artifact}");
        assert!(
            !artifact.contains("LimAnonymousRecordPending"),
            "{artifact}"
        );
        for registration in &manifests[0].registrations {
            let span = registration
                .generated_handler
                .expect("nested direct-call handler origin");
            assert_eq!(span.source_id, manifests[0].source_id);
            assert_eq!(&artifact[span.start..span.end], registration.handler);
        }
        if let Some((path, text)) = &previous {
            assert_eq!(path, &manifests[0].generated_path);
            assert_eq!(
                text, &artifact,
                "warm cache must compile the same readable source"
            );
        }
        previous = Some((manifests[0].generated_path.clone(), artifact));
        let binary = root.join(format!("program-{pass}"));
        lim::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let (status, stdout, stderr) =
            support::run(&mut Command::new(&binary), Duration::from_secs(5), 4096).unwrap();
        assert_eq!(status.code(), Some(42), "{stderr:?}\n{source}");
        assert!(stdout.is_empty());
        assert!(stderr.is_empty());
        last = manifests;
    }
    last
}

#[test]
fn dispatch_record_signatures_match_aliases_and_reordered_fields_across_files() {
    let scratch = support::Scratch::new("anonymous-dispatch-aliases");
    fs::write(scratch.path().join("handlers.lim"), r#"
#type Number #u64
#type Result { value = Number; consumed = #usize; }
#fn handle { #params = { counter = (#ref-mut #usize); context = { offset = Number; }; input = Number; };
  #returns = Result;
  #body:
    #deref-set counter (#usize::add-wrap (#deref counter) 1usize);
    #return (#record-literal { consumed = #usize; value = #u64; }
      { value = (#u64::add-wrap input (#get context offset)); consumed = (#deref counter); });
}
"#).unwrap();
    let source = r#"
#alias handle = ./handlers.lim::handle
#enum Choice () ((Choice.Full #u64))
#dispatch-fn evaluate {
  #params = { input = Choice; context = { offset = #u64; }; counter = (#ref-mut #usize); };
  #returns = { consumed = #usize; value = #u64; };
  #dispatch-on = input;
}
#dispatch-case evaluate Choice.Full handle
#fn main { #params = {}; #returns = #u64;
  #body:
    #let-mut counter #usize 0usize;
    #let { value = (#bind answer #u64); consumed = (#bind calls #usize); }
      = (evaluate { counter = (#borrow-mut counter);
          context = (#record-literal { offset = #u64; } { offset = 2u64; });
          input = (Choice.Full 40u64); });
    #assert (#usize::eq counter 1usize);
    #assert (#usize::eq calls 1usize);
    #return answer;
}
"#;
    let manifests = run_fresh_and_cached(source, scratch.path());
    let artifact = fs::read_to_string(&manifests[0].generated_path).unwrap();
    assert!(artifact.contains("consumed = #usize;"), "{artifact}");
    assert!(artifact.contains("value = #u64;"), "{artifact}");
    assert!(artifact.contains("offset = #u64;"), "{artifact}");
    assert!(manifests[0].registrations[0]
        .handler
        .ends_with("handlers.lim::handle"));
    // The empty product is unit. The caller still explicitly accounts for
    // its zero fields, and cached dispatch code keeps an explicit unit return.
    let empty = r#"
#enum Choice () (Choice.Empty)
#dispatch-fn empty { #params = { value = Choice; }; #returns = {}; #dispatch-on = value; }
#dispatch-case empty Choice.Empty handle
#fn handle { #params = {}; #returns = {}; #body: #return (#record-literal {} {}); }
#fn main { #params = {}; #returns = #u64;
  #body = ((#let {} = (empty { value = Choice.Empty; })) (#return 42u64)); }
"#;
    run_cached_result(empty, scratch.path(), false);
}

#[test]
fn dispatch_record_results_move_every_linear_field_once() {
    let scratch = support::Scratch::new("anonymous-dispatch-linear");
    let source = r#"
#struct Token (#linear) ((number #u64))
#type Owned Token
#enum Choice (#linear) ((Choice.Full Token))
#dispatch-fn take { #params = { value = Choice; };
  #returns = { token = Token; count = #usize; }; #dispatch-on = value; }
#dispatch-case take Choice.Full handle
#fn handle { #params = { value = Token; }; #returns = { count = #usize; token = Owned; };
  #body: #return (#record-literal { token = Token; count = #usize; }
    { count = 1usize; token = value; }); }
#fn main { #params = {}; #returns = #u64;
  #body:
    #let { count = (#ignore #usize); token = (#bind owned Owned); }
      = (take { value = (Choice.Full (#struct-literal Token { number = 42u64; })); });
    #let answer #u64 (#get owned number);
    #forget owned;
    #return answer;
}
"#;
    run_fresh_and_cached(source, scratch.path());
    let doubled = source.replace("#forget owned;", "#forget owned; #forget owned;");
    let error = compile(&doubled, scratch.path()).unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Linear);
    assert!(error.message.contains("already consumed"), "{error:?}");
    let span = error
        .span
        .expect("linear error keeps the second consume location");
    assert_eq!(&doubled[span.start..span.end], "owned");
}

#[test]
fn dispatch_record_reference_fields_keep_distinct_borrow_origins() {
    let scratch = support::Scratch::new("anonymous-dispatch-references");
    let source = r#"
#enum Choice () (Choice.Views)
#dispatch-fn views { #params = { value = Choice; left = (#ref #u64); right = (#ref-mut #u64); };
  #returns = { exclusive = (#ref-mut #u64); shared = (#ref #u64); }; #dispatch-on = value; }
#dispatch-case views Choice.Views handle
#fn handle { #params = { right = (#ref-mut #u64); left = (#ref #u64); };
  #returns = { shared = (#ref #u64); exclusive = (#ref-mut #u64); };
  #body: #return (#record-literal { shared = (#ref #u64); exclusive = (#ref-mut #u64); }
    { shared = left; exclusive = right; }); }
#fn main { #params = {}; #returns = #u64;
  #body:
    #let-mut left #u64 20u64;
    #let-mut right #u64 22u64;
    #let { shared = (#bind shared (#ref #u64)); exclusive = (#bind exclusive (#ref-mut #u64)); }
      = (views { value = Choice.Views; left = (#borrow left); right = (#borrow-mut right); });
    #deref-set exclusive 22u64;
    #let answer #u64 (#u64::add-wrap (#deref shared) (#deref exclusive));
    #drop shared; #drop exclusive;
    #set left 0u64; #set right 0u64;
    #return answer;
}
"#;
    run_fresh_and_cached(source, scratch.path());
    for value in ["left", "right"] {
        let invalid = source.replace(
            "#deref-set exclusive 22u64;",
            &format!("#set {value} 0u64; #deref-set exclusive 22u64;"),
        );
        let error = compile(&invalid, scratch.path()).unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        assert!(error.span.is_some());
    }
}

#[test]
fn borrowed_dispatch_payload_can_return_a_record_view_without_losing_the_loan() {
    let scratch = support::Scratch::new("anonymous-dispatch-borrowed-payload");
    let source = r#"
#struct Payload () ((number #u64))
#enum Choice () ((Choice.Full Payload))
#type Result { view = (#ref #u64); }
#dispatch-fn inspect { #params = { value = (#ref Choice); };
  #returns = Result; #dispatch-on = value; }
#dispatch-case inspect Choice.Full handle
#fn handle { #params = { value = (#ref Payload); }; #returns = Result;
  #body: #return (#record-literal { view = (#ref #u64); }
    { view = (#borrow (#get value number)); }); }
#fn main { #params = {}; #returns = #u64;
  #body:
    #let-mut item Choice (Choice.Full (#struct-literal Payload { number = 42u64; }));
    #let { view = (#bind view (#ref #u64)); } = (inspect { value = (#borrow item); });
    #let answer #u64 (#deref view);
    #drop view;
    #set item (Choice.Full (#struct-literal Payload { number = 0u64; }));
    #return answer;
}
"#;
    let original = run_fresh_and_cached(source, scratch.path());
    let invalid = source.replace("#let answer #u64 (#deref view);", "#set item (Choice.Full (#struct-literal Payload { number = 0u64; })); #let answer #u64 (#deref view);");
    let error = compile(&invalid, scratch.path()).unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some());
    let changed = source
        .replace(
            "#type Result { view = (#ref #u64); }",
            "#type Result { count = #u64; view = (#ref #u64); }",
        )
        .replace(
            "#record-literal { view = (#ref #u64); }",
            "#record-literal { count = #u64; view = (#ref #u64); }",
        )
        .replace(
            "{ view = (#borrow (#get value number)); }",
            "{ count = 1u64; view = (#borrow (#get value number)); }",
        )
        .replace(
            "#let { view = (#bind view (#ref #u64)); }",
            "#let { count = (#ignore #u64); view = (#bind view (#ref #u64)); }",
        );
    let revised = run_fresh_and_cached(&changed, scratch.path());
    assert_ne!(
        original[0].generated_path, revised[0].generated_path,
        "a changed layout behind the same alias must replace the cached implementation"
    );
}
