mod support;

use std::{process::Command, time::Duration};

fn source(ty: &str, arms: &str) -> String {
    format!("#fn classify {{\n  #params = ((value #{ty}));\n  #returns = #u64;\n  #body = ( (#return (#match value {arms}))\n  );\n}}\n")
}

fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source).unwrap())
}

fn accepts(ty: &str, arms: &str) {
    check(&source(ty, arms)).unwrap_or_else(|error| panic!("{error}\n{arms}"));
}

fn rejects(ty: &str, arms: &str) {
    let error = check(&source(ty, arms)).expect_err("uncovered values must be rejected");
    assert!(error.contains("not exhaustive"), "{error}");
}

#[test]
fn complete_integer_domains_and_split_ranges_need_no_wildcard() {
    for (ty, minimum, maximum) in [
        ("u8", "0", "255"),
        ("u16", "0", "65535"),
        ("u32", "0", "4294967295"),
        ("u64", "0", "18446744073709551615"),
        ("usize", "0", "18446744073709551615"),
        ("u128", "0", "340282366920938463463374607431768211455"),
        ("i8", "-128", "127"),
        ("i16", "-32768", "32767"),
        ("i32", "-2147483648", "2147483647"),
        ("i64", "-9223372036854775808", "9223372036854775807"),
        ("isize", "-9223372036854775808", "9223372036854775807"),
        (
            "i128",
            "-170141183460469231731687303715884105728",
            "170141183460469231731687303715884105727",
        ),
    ] {
        accepts(
            ty,
            &format!("(#case (#range {minimum}{ty} {maximum}{ty}) 42u64)"),
        );
        accepts(ty, &format!("(#case (#range 1{ty} {maximum}{ty}) 42u64) (#case (#range {minimum}{ty} 0{ty}) 0u64)"));
        rejects(ty, &format!("(#case (#range 1{ty} {maximum}{ty}) 42u64)"));
        rejects(
            ty,
            &format!("(#case (#range {minimum}{ty} {maximum}{ty}) (#when false) 42u64)"),
        );
    }
}

#[test]
fn literals_or_patterns_and_overlapping_ranges_combine_coverage() {
    for ty in ["u8", "i8"] {
        let minimum = if ty == "u8" { 0 } else { -128 };
        let arms = (minimum..minimum + 256)
            .map(|value| format!("(#case {value}{ty} 42u64)"))
            .collect::<Vec<_>>()
            .join(" ");
        accepts(ty, &arms);
        rejects(ty, &arms.replace(&format!("(#case 42{ty} 42u64)"), ""));
    }
    accepts(
        "u8",
        "(#case (#or (#range 128u8 255u8) (#or 0u8 (#range 1u8 127u8))) 42u64)",
    );
    accepts(
        "u8",
        "(#case (#range 100u8 255u8) 42u64) (#case (#range 0u8 150u8) 0u64)",
    );
    accepts("u8", "(#case (#or 1u8 (#or _ 2u8)) 42u64)");
    rejects(
        "u8",
        "(#case (#range 0u8 126u8) 42u64) (#case (#range 128u8 255u8) 0u64)",
    );
    rejects("u8", "(#case (#range 0u8 254u8) 42u64)");
    rejects("u128", "(#case (#range 0u128 170141183460469231731687303715884105727u128) 0u64) (#case (#range 170141183460469231731687303715884105729u128 340282366920938463463374607431768211455u128) 1u64)");
}

#[test]
fn guarded_patterns_do_not_establish_unconditional_coverage() {
    rejects(
        "bool",
        "(#case true (#when false) 1u64) (#case false (#when false) 2u64)",
    );
    rejects("bool", "(#case (#or true false) (#when true) 1u64)");
    rejects("bool", "(#case true 1u64) (#case false (#when false) 2u64)");
    accepts(
        "bool",
        "(#case true (#when false) 1u64) (#case true 2u64) (#case false 3u64)",
    );
    accepts("bool", "(#case (#or (#or true false)) 42u64)");
    rejects(
        "u8",
        "(#case (#range 0u8 254u8) 0u64) (#case 255u8 (#when false) 1u64)",
    );
    rejects("u8", "(#case (#or _ 0u8) (#when true) 1u64)");
    accepts(
        "u8",
        "(#case (#range 0u8 254u8) 0u64) (#case 255u8 (#when false) 1u64) (#case 255u8 42u64)",
    );
    accepts(
        "char",
        "(#case #\\a (#when false) 1u64) (#case #\\a 2u64) (#case _ 3u64)",
    );
}

fn run(program: &str) {
    let scratch = support::Scratch::new("integer-match-coverage");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        program,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
    .unwrap_or_else(|error| panic!("{error:?}\n{program}"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{status:?}\n{stderr:?}\n{program}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

#[test]
fn exhaustive_matches_dispatch_all_u8_values_and_full_width_boundaries() {
    let mut program = source(
        "u8",
        "(#case (#range 0u8 127u8) 0u64) (#case (#range 128u8 255u8) 1u64)",
    );
    program.push_str("#fn main () #u64");
    for value in 0..=255 {
        program.push_str(&format!(
            "(#assert (#u64::eq (#call classify ((value {value}u8))) {}u64))",
            usize::from(value >= 128)
        ));
    }
    program.push_str("  (#return 42u64)");
    run(&program);
    for (ty, minimum, maximum) in [
        ("u64", "0", "18446744073709551615"),
        ("i64", "-9223372036854775808", "9223372036854775807"),
        ("u128", "0", "340282366920938463463374607431768211455"),
        (
            "i128",
            "-170141183460469231731687303715884105728",
            "170141183460469231731687303715884105727",
        ),
    ] {
        let program = format!("{}#fn main () #u64 (#assert (#u64::eq (#call classify ((value {minimum}{ty}))) 42u64)) (#return (#call classify ((value {maximum}{ty}))))\n", source(ty, &format!("(#case (#range {minimum}{ty} {maximum}{ty}) 42u64)")));
        run(&program);
    }
    run("#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#match true (#case true (#when false) 0u64) (#case true 42u64) (#case false 1u64)))\n  );\n}\n");
}
