mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};
use std::{fs, path::Path, process::Command, time::Duration};

fn compile(dir: &Path, source: &str) -> (Result<String, lim::Diagnostic>, String) {
    lim::with_cache_report(|| {
        lim::compile_source_with_generated_sources(
            source,
            &dir.join("main.lim"),
            &CompileConfig::default(),
            &dir.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
            None,
            &dir.join("generated"),
        )
    })
}

fn hits(report: &str) -> usize {
    report
        .split("\"kind\":\"semantic-summary\"")
        .skip(1)
        .filter(|part| {
            part.split('}')
                .next()
                .unwrap()
                .contains("\"decision\":\"hit\"")
        })
        .count()
}

fn native_42(dir: &Path, assembly: &str) {
    let binary = dir.join("program");
    lim::link_native_binary(
        assembly,
        &binary,
        &[],
        &[],
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, out, err) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{err:?}");
    assert!(out.is_empty() && err.is_empty());
}

// The oracle is the language contract: a carried reference prevents owner
// mutation until every copied handle is retired. No second compiler is used.
#[test]
fn aliases_aggregate_returns_and_generated_helpers_preserve_loans() {
    for generated in [false, true] {
        for (shape, ty, value, extract) in [
            (
                "struct",
                "Holder",
                "(#struct-literal Holder ((view input)))",
                "(#get carried view)",
            ),
            (
                "tuple",
                "(#tuple (#ref #u64) #u64)",
                "(#tuple input 0u64)",
                "(#get carried 0)",
            ),
            (
                "array",
                "(#array (#ref #u64) 1)",
                "(#array-of (#array (#ref #u64) 1) input)",
                "(#index carried 0usize)",
            ),
        ] {
            for action in ["release", "disjoint", "overlap"] {
                let name = format!("ownership-{generated}-{shape}-{action}");
                let scratch = support::Scratch::new(&name);
                let dir = scratch.path();
                let helper = format!("#fn carry {{\n  #params = ((input (#ref #u64)));\n  #returns = {ty};\n  #body = ( (#return {value})\n  );\n}}\n");
                let library = format!(
                    "#struct Holder () ((view (#ref #u64)))\n{}",
                    if generated {
                        format!("#gn emit {{}} `(({helper}))\n#generate emit {{}}\n")
                    } else {
                        helper
                    }
                );
                fs::write(dir.join("lib.lim"), library).unwrap();
                let operation = match action {
                    "release" => "(#forget alias) (#set owner 42u64)",
                    "disjoint" => "(#set other 9u64)",
                    _ => "(#set owner 9u64)",
                };
                let finish = if action == "release" {
                    "(#return owner)"
                } else {
                    "(#let answer #u64 (#deref alias)) (#forget alias) (#return answer)"
                };
                let source = format!(
                    "#alias Holder = ./lib.lim::Holder
#alias forwarded = ./lib.lim::carry
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                        (#let-mut owner #u64 42u64) (#let-mut other #u64 0u64)
                        (#let carried {ty} (#call forwarded ((input (#borrow owner)))))
                        (#let alias (#ref #u64) {extract}) (#forget carried)
                        {operation} {finish}\n  );\n}}\n"
                );
                let (cold, cold_report) = compile(dir, &source);
                let (warm, warm_report) = compile(dir, &source);
                assert_eq!(hits(&cold_report), 0, "{name}");
                if action == "overlap" {
                    let error = cold.expect_err(&name);
                    assert_eq!(error.code, DiagnosticCode::Borrow, "{name}: {error:?}");
                    assert_eq!(warm.unwrap_err(), error, "{name}");
                    // Also challenge a cache warmed by a valid sibling program.
                    let control = source.replace("(#set owner 9u64)", "(#set other 9u64)");
                    compile(dir, &control).0.unwrap();
                    assert_eq!(compile(dir, &source).0.unwrap_err(), error, "{name}");
                } else {
                    let assembly = cold.unwrap_or_else(|e| panic!("{name}: {e:?}"));
                    assert_eq!(warm.unwrap(), assembly, "{name}");
                    assert!(hits(&warm_report) > 0, "{name}: {warm_report}");
                    native_42(dir, &assembly);
                }
            }
        }
    }
}

// Explicit #linear makes this owner linear despite its Copy scalar payload.
// Moving it through a generated/imported identity must not duplicate it.
#[test]
fn aggregate_owner_transfer_requires_exactly_one_consumption() {
    for generated in [false, true] {
        for action in ["once", "twice", "leak", "borrowed", "released"] {
            let name = format!("linear-transfer-{generated}-{action}");
            let scratch = support::Scratch::new(&name);
            let dir = scratch.path();
            let helper = "#fn transfer {\n  #params = ((input Token));\n  #returns = Token;\n  #body = ( (#return input)\n  );\n}\n";
            let library = format!(
                "#struct Token (#linear) ((value #u64))\n{}",
                if generated {
                    format!("#gn emit {{}} `(({helper}))\n#generate emit {{}}\n")
                } else {
                    helper.to_owned()
                }
            );
            fs::write(dir.join("lib.lim"), library).unwrap();
            let consumption = match action {
                "once" | "released" => "(#forget moved)",
                "borrowed" => "(#let answer #u64 (#deref view)) (#forget view) (#forget moved)",
                "twice" => "(#forget moved) (#forget moved)",
                _ => "",
            };
            let borrow = match action {
                "borrowed" => "(#let view (#ref #u64) (#borrow (#get owner value)))",
                "released" => "(#let view (#ref #u64) (#borrow (#get owner value))) (#forget view)",
                _ => "",
            };
            let source = format!(
                "#alias Token = ./lib.lim::Token
#alias forwarded = ./lib.lim::transfer
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                    (#let owner Token (#struct-literal Token ((value 42u64))))
                    {borrow}
                    (#let moved Token (#call forwarded ((input owner))))
                    {consumption} (#return 42u64)\n  );\n}}\n"
            );
            let (cold, _) = compile(dir, &source);
            let (warm, report) = compile(dir, &source);
            if matches!(action, "once" | "released") {
                let assembly = cold.unwrap();
                assert_eq!(warm.unwrap(), assembly);
                assert!(hits(&report) > 0, "{name}: {report}");
                native_42(dir, &assembly);
            } else {
                let error = cold.expect_err(&name);
                // A post-transfer field alias reads a consumed linear referent.
                assert_eq!(error.code, DiagnosticCode::Linear, "{name}: {error:?}");
                assert_eq!(warm.unwrap_err(), error, "{name}");
            }
        }
    }
}
