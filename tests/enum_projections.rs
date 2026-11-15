mod support;

use lim::{check_types, parse_program};
use std::{fs, process::Command, time::Duration};

const MODES: [(&str, &str); 4] = [
    ("ref", "borrow"),
    ("ref-mut", "borrow-mut"),
    ("pin-ref", "pin-borrow"),
    ("pin-ref-mut", "pin-borrow-mut"),
];

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

fn declaration(mode: &str) -> String {
    format!("#std
#enum Choice () ((Choice.Full #u64) Choice.Empty)
#generate #enum-project ((enum Choice) (variant Choice.Full) (payload #u64) (mode #{mode}) (name Projection))
")
}

fn run(source: &str, answer: i32) {
    check(source).unwrap();
    let scratch = support::Scratch::new("enum-projection");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        64 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) =
        support::run(&mut Command::new(&binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(answer), "{source}: {stderr:?}");
}

#[test]
fn every_mode_generates_only_the_selected_signature_and_handles_both_variants() {
    for (mode, borrow) in MODES {
        for (value, answer) in [("(Choice.Full 42u64)", 42), ("Choice.Empty", 7)] {
            let source = format!(
                "{}
#fn main () #u64
                  (#let-mut owner Choice {value})
                  (#let-else (Projection.Some payload)
                    (#call Projection::project ((source (#{borrow} owner))))
                    (#else (#return 7u64)))
                  (#return (#deref payload))
",
                declaration(mode)
            );
            let program = parse_program(&source).unwrap();
            let functions = program
                .items
                .iter()
                .filter_map(|item| match item {
                    lim::Item::Function(function)
                        if function
                            .name
                            .rsplit(".lim::")
                            .next()
                            .unwrap()
                            .starts_with("Projection::") =>
                    {
                        Some(function)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(functions.len(), 1);
            assert!(functions[0].name.ends_with("Projection::project"));
            run(&source, answer);
        }
    }
}

#[test]
fn optional_payloads_retain_the_owner_loan_and_selected_mutability() {
    for (mode, borrow) in MODES {
        let source = format!(
            "{}
#fn main () #u64 (#let-mut owner Choice (Choice.Full 42u64))
              (#let-else (Projection.Some payload)
                (#call Projection::project ((source (#{borrow} owner))))
                (#else (#return 0u64)))
              (#set owner Choice.Empty) (#return (#deref payload))
",
            declaration(mode)
        );
        for invalid in [
            source.clone(),
            source.replace("(#set owner Choice.Empty)", "(#forget owner)"),
        ] {
            let error = check(&invalid).unwrap_err();
            assert!(
                error.contains("borrow") || error.contains("pinned"),
                "{mode}: {error}"
            );
        }
        let writing = source.replace("(#set owner Choice.Empty)", "(#deref-set payload 42u64)");
        assert_eq!(check(&writing).is_ok(), mode == "ref-mut", "{mode}");
    }
}

#[test]
fn an_undestructured_optional_keeps_the_loan_and_unreferenceable_payloads_are_rejected() {
    for (mode, borrow) in MODES {
        let source = format!(
            "{}
#fn main () #u64 (#let-mut owner Choice (Choice.Full 42u64))
              (#let projected Projection (#call Projection::project ((source (#{borrow} owner)))))
              (#forget owner)
              (#let-else (Projection.Some payload) projected (#else (#return 0u64)))
              (#return (#deref payload))
",
            declaration(mode)
        );
        let error = check(&source).unwrap_err();
        assert!(
            error.contains("borrow") || error.contains("pinned"),
            "{mode}: {error}"
        );
        let error = check(&format!("#alias lim-gen-enum-project = /<lim-std>/enum_project.lim::#enum-project\n#enum Choice () ((Choice.HasUnit ()) Choice.Empty)\n#generate lim-gen-enum-project ((enum Choice) (variant Choice.HasUnit) (payload ()) (mode #{mode}) (name Projection))\n#fn main () #u64 (#let-mut owner Choice (Choice.HasUnit ()))\n              (#let-else (Projection.Some payload)\n                (#call Projection::project ((source (#{borrow} owner)))) (#else (#return 0u64)))\n              (#let value () (#deref payload)) (#forget value)\n              (#return 42u64)\n")).unwrap_err();
        assert!(
            error.contains("reference target other than () or #never"),
            "{error}"
        );
    }
}

#[test]
fn returning_projected_references_preserves_origins_and_rejects_local_escape() {
    for (mode, borrow) in MODES {
        let source = format!(
            "{}
#fn project ((source (#{mode} Choice)) (fallback (#{mode} #u64))) (#{mode} #u64)
              (#let-else (Projection.Some payload)
                (#call Projection::project ((source source)))
                (#else (#return fallback)))
              (#return payload)
",
            declaration(mode)
        );
        check(&source).unwrap();
        let local = source
            .replace(
                "(#let-else (Projection.Some payload)",
                "(#let-mut local Choice (Choice.Full 42u64)) (#let-else (Projection.Some payload)",
            )
            .replace("(source source)", &format!("(source (#{borrow} local))"));
        let error = check(&local).unwrap_err();
        assert!(
            error.contains("borrow") || error.contains("local"),
            "{mode}: {error}"
        );
    }
}

#[test]
fn a_mismatch_can_project_the_other_variant_and_destroy_the_linear_owner() {
    let source = "#std
#struct Resource (#linear) ((value #u64))
#enum Choice () ((Choice.Full Resource) (Choice.Other Resource))
#generate #enum-project ((enum Choice) (variant Choice.Full) (payload Resource) (mode #pin-ref-mut) (name FullView))
#generate #enum-project ((enum Choice) (variant Choice.Other) (payload Resource) (mode #pin-ref-mut) (name OtherView))
#fn main () #u64
          (#let-mut owner Choice (Choice.Other (#struct-literal Resource ((value 42u64)))))
          (#let-else (FullView.Some payload)
            (#call FullView::project ((source (#pin-borrow-mut owner))))
            (#else
              (#let-else (OtherView.Some failure)
                (#call OtherView::project ((source (#pin-borrow-mut owner))))
                (#else (#forget owner) (#return 0u64)))
              (#let answer #u64 (#get failure value))
              (#drop failure) (#forget owner) (#return answer)))
          (#drop payload) (#forget owner) (#return 0u64)\n";
    run(source, 42);
}

#[test]
fn aliases_generated_declarations_and_external_prefixes_obey_normal_checking() {
    let scratch = support::Scratch::new("projection-import");
    fs::write(scratch.path().join("library.lim"), "#alias lim-gen-enum-project = /<lim-std>/enum_project.lim::#enum-project\n#gn declare () `((#enum Choice () ((Choice.Full #u64) Choice.Empty)) (#type View (#pin-ref Choice)))\n#generate declare\n#generate lim-gen-enum-project ((enum Choice) (variant Choice.Full) (payload #u64) (mode #pin-ref) (name Projection))\n#fn read ((input View)) #u64\n          (#let-else (Projection.Some value)\n            (#call Projection::project ((source input))) (#else (#return 0u64)))\n          (#return (#deref value))\n").unwrap();
    let source =
        "#alias ExtChoice = ./library.lim::Choice
#alias ext@read = ./library.lim::read
#fn main () #u64 (#let owner ExtChoice (ExtChoice.Full 42u64))
          (#return (#call ext@read ((input (#pin-borrow owner)))))\n";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    check_types(&program).unwrap();
}

#[test]
fn projected_async_protocol_payloads_do_not_require_generator_dependency_order() {
    check("#std
#generate #enum-project ((enum Work::Poll) (variant Work::Poll.Ready) (payload #u64) (mode #ref) (name ReadyView))
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64) (function (#fn work () #u64 (#return 42u64))))
#fn read ((input (#ref Work::Poll))) #u64
          (#let-else (ReadyView.Some value)
            (#call ReadyView::project ((source input))) (#else (#return 0u64)))
          (#return (#deref value))
#fn main () #u64 (#return 0u64)\n").unwrap();
}

#[test]
fn invalid_modes_payloads_receivers_and_removed_keywords_are_rejected() {
    let valid = format!(
        "{}#fn main () #u64
        (#let-mut owner Choice (Choice.Full 42u64))
        (#let-else (Projection.Some value)
          (#call Projection::project ((source (#pin-borrow-mut owner)))) (#else (#return 0u64)))
        (#return (#deref value))\n",
        declaration("pin-ref-mut")
    );
    check(&valid).unwrap();
    for invalid in [
        valid.replace("(mode #pin-ref-mut)", "(mode #ptr-mut)"),
        valid.replace("(payload #u64)", "(payload #u32)"),
        valid.replace("(variant Choice.Full)", "(variant Choice.Empty)"),
        valid.replace("(#pin-borrow-mut owner)", "(#pin-borrow owner)"),
        valid.replace("(#pin-borrow-mut owner)", "(#borrow-mut owner)"),
        valid.replace("(#else (#return 0u64))", "(#else ())"),
    ] {
        assert!(check(&invalid).is_err(), "{invalid}");
    }
    for removed in [
        "#let-else-ref",
        "#let-else-ref-mut",
        "#let-else-pin",
        "#let-else-pin-mut",
    ] {
        let source = format!(
            "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn main () #u64 (#let-mut owner Choice (Choice.Full 42u64))
              ({removed} (Choice.Full value) (#pin-ref-mut Choice) (#pin-borrow-mut owner) (#return 0u64))
              (#return (#deref value))\n"
        );
        assert!(
            check(&source).is_err(),
            "removed keyword accepted: {removed}"
        );
    }
    assert!(check("#std\n#generate #pin-project ()\n").is_err());
}
