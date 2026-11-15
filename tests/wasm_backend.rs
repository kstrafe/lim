mod support;
use lim::wasm;
use std::{fs, process::Command, time::Duration};

fn run(source: &str, expected: &str) {
    let module = wasm::compile(source)
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, source, "test.lim")));
    assert_eq!(
        module.bytes,
        wasm::compile(source).unwrap().bytes,
        "emission must be deterministic"
    );
    let scratch = support::Scratch::new("wasm");
    let path = scratch.path().join("program.wasm");
    fs::write(&path, module.bytes).unwrap();
    let kind = format!("{:?}", module.return_type);
    let script = "const fs=require('node:fs'); (async()=>{const bytes=fs.readFileSync(process.argv[1]); const mod=new WebAssembly.Module(bytes); if(WebAssembly.Module.imports(mod).length)throw Error('unexpected host imports'); const instance=new WebAssembly.Instance(mod,{}); let result=instance.exports.main(); if(process.argv[2]==='Unsigned64')result=BigInt.asUintN(64,result); if(process.argv[2]==='Bool')result=!!result; console.log(result===undefined?'()':String(result));})().catch(e=>{console.error(e);process.exitCode=1;});";
    let (status, out, err) = support::run(
        Command::new("node")
            .arg("-e")
            .arg(script)
            .arg(path)
            .arg(kind),
        Duration::from_secs(5),
        8192,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&err));
    assert_eq!(String::from_utf8(out).unwrap().trim(), expected);
}
#[test]
fn native_engine_executes_typed_scalar_functions_and_named_calls() {
    run("#fn subtract { #params = { left = #u64; right = #u64; }; #returns = #u64; #body: #return : #u64::sub-wrap left right; }\n#fn main { #params = {}; #returns = #u64; #body: #return subtract { right = 2; left = 44; }; }", "42");
    run(
        "(#fn main () #u64 (#return (#u64::add-wrap 18446744073709551615u64 1u64)))",
        "0",
    );
    run(
        "(#fn main () #u64 (#return 18446744073709551615u64))",
        "18446744073709551615",
    );
    run(
        "(#fn main () #i64 (#return (#i64::div-wrap -9223372036854775808i64 -1i64)))",
        "-9223372036854775808",
    );
    run(
        "(#fn main () #bool (#return (#i64::lt -2i64 1i64)))",
        "true",
    );
    run("(#fn main () () (#return ()))", "()");
    run(
        "(#fn main () #u64 (#return (#call #u64::add-wrap ((right 22u64) (left 20u64)))))",
        "42",
    );
    run("(#fn choose ((ignored ()) (number #u64)) #u64 (#return number)) (#fn main () #u64 (#return (#call choose ((number 42u64) (ignored ())))))", "42");
}
#[test]
fn loops_keep_continue_break_and_block_depth_correct() {
    run("(#fn main () #u64 (#let-mut total #u64 0u64) (#for-range (number #u64) 1u64 11u64 (#if (#u64::eq number 5u64) (#block (#continue)) ()) (#set total (#u64::add-wrap total number))) (#return total))", "50");
    run("(#fn main () #u64 (#let-mut value #u64 0u64) (#while true (#set value (#u64::add-wrap value 1u64)) (#if (#u64::eq value 42u64) (#block (#break)) ())) (#return value))", "42");
    run("(#fn main () #u64 (#return (#block (#let value #u64 40u64) (#if true (#u64::add-wrap value 2u64) 0u64))))", "42");
}
#[test]
fn boolean_operators_short_circuit_and_preserve_bits() {
    run("(#fn bad () #bool (#return (#panic))) (#fn main () #bool (#return (#bool::or true (#call bad ()))))", "true");
    run(
        "(#fn main () #u64 (#return (#u64::bit-xor (#u64::shl 5u64 3u64) 2u64)))",
        "42",
    );
    run(
        "(#fn main () #u64 (#return (#u64::not 0u64)))",
        "18446744073709551615",
    );
}
#[test]
fn contract_evidence_and_audits_use_the_normal_frontend() {
    run("(#fn identity ((n #u64)) #u64 (#ensures (#u64::eq (#result) n)) (#return n)) (#fn main () #u64 (#return (#call identity ((n 42u64)))))", "42");
    let source = "(#fn positive ((n #u64)) #bool (#return (#u64::gt n 0u64))) (#fn use ((n #u64)) #u64 (#requires (#call positive ((n n)))) (#return n)) (#fn main () #u64 (#let n #u64 42u64) (#return (#if-valid (#call positive ((n n))) (#call use ((n n))) 0u64)))";
    run(source, "42");
    let error = wasm::compile(&source.replace(
        "(#if-valid (#call positive ((n n))) (#call use ((n n))) 0u64)",
        "(#call use ((n n)))",
    ))
    .err()
    .unwrap();
    assert_eq!(error.code, lim::DiagnosticCode::Contract);
}
#[test]
fn checker_accepts_broader_programs_and_backend_fails_explicitly() {
    let source = "(#fn main () #u64 (#let items (#array #u64 2) (#array-of (#array #u64 2) 20u64 42u64)) (#return (#index items 1usize)))";
    wasm::check(source).unwrap();
    let error = wasm::compile(source).err().unwrap();
    assert_eq!(error.code, lim::DiagnosticCode::Codegen);
    assert!(error.message.contains("does not yet support"));
    assert!(wasm::check("(#alias value = /tmp/private.lim::value)")
        .unwrap_err()
        .message
        .contains("file imports"));
    assert!(wasm::compile(&" ".repeat(wasm::MAX_SOURCE_BYTES + 1)).is_err());
    assert!(wasm::compile("(#fn main () #u64 (#return false))").is_err());
}

#[test]
fn syntax_diagnostics_keep_native_phase_codes_and_source_locations() {
    for (source, code) in [
        ("\"unfinished", lim::DiagnosticCode::Lex),
        ("(#fn main", lim::DiagnosticCode::Parse),
    ] {
        let diagnostic = wasm::check(source).unwrap_err();
        assert_eq!(diagnostic.code, code);
        assert!(diagnostic.span.is_some());
        assert_eq!(diagnostic.source_text.as_deref(), Some(source));
    }
}
