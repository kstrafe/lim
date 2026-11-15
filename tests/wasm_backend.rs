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
        "#fn main () #u64 (#return (#u64::add-wrap 18446744073709551615u64 1u64))\n",
        "0",
    );
    run(
        "#fn main () #u64 (#return 18446744073709551615u64)\n",
        "18446744073709551615",
    );
    run(
        "#fn main () #i64 (#return (#i64::div-wrap -9223372036854775808i64 -1i64))\n",
        "-9223372036854775808",
    );
    run(
        "#fn main () #bool (#return (#i64::lt -2i64 1i64))\n",
        "true",
    );
    run("#fn main () () (#return ())\n", "()");
    run(
        "#fn main () #u64 (#return (#call #u64::add-wrap ((right 22u64) (left 20u64))))\n",
        "42",
    );
    run("#fn choose ((ignored ()) (number #u64)) #u64 (#return number)\n#fn main () #u64 (#return (#call choose ((number 42u64) (ignored ()))))\n", "42");
}
#[test]
fn named_values_stage_in_written_order_before_parameter_marshalling() {
    for parameters in ["(left #u64) (right #u64)", "(right #u64) (left #u64)"] {
        let source = format!(
            "#fn subtract ({parameters}) #u64
              (#return (#u64::sub-wrap left right))
#fn main () #u64 (#let-mut step #u64 0u64)
              (#let answer #u64 (#call subtract
                ((right (#block (#assert (#u64::eq step 0u64)) (#set step 1u64) 2u64))
                 (left (#block (#assert (#u64::eq step 1u64)) (#set step 2u64) 44u64)))))
              (#assert (#u64::eq step 2u64)) (#return answer)\n"
        );
        run(&source, "42");
        run(
            &source.replace("#call subtract", "#call #u64::sub-wrap"),
            "42",
        );
    }
}

#[test]
fn loops_keep_continue_break_and_block_depth_correct() {
    run("#fn main () #u64 (#let-mut total #u64 0u64) (#for-range (number #u64) 1u64 11u64 (#if (#u64::eq number 5u64) (#block (#continue)) ()) (#set total (#u64::add-wrap total number))) (#return total)\n", "50");
    run("#fn main () #u64 (#let-mut value #u64 0u64) (#while true (#set value (#u64::add-wrap value 1u64)) (#if (#u64::eq value 42u64) (#block (#break)) ())) (#return value)\n", "42");
    run("#fn main () #u64 (#return (#block (#let value #u64 40u64) (#if true (#u64::add-wrap value 2u64) 0u64)))\n", "42");
}
#[test]
fn boolean_operators_short_circuit_and_preserve_bits() {
    run("#fn bad () #bool (#return (#panic))\n#fn main () #bool (#return (#bool::or true (#call bad ())))\n", "true");
    run(
        "#fn main () #u64 (#return (#u64::bit-xor (#u64::shl 5u64 3u64) 2u64))\n",
        "42",
    );
    run(
        "#fn main () #u64 (#return (#u64::not 0u64))\n",
        "18446744073709551615",
    );
}
#[test]
fn contract_evidence_and_audits_use_the_normal_frontend() {
    run("#fn identity ((n #u64)) #u64 (#ensures (#u64::eq (#result) n)) (#return n)\n#fn main () #u64 (#return (#call identity ((n 42u64))))\n", "42");
    let source = "#fn positive ((n #u64)) #bool (#return (#u64::gt n 0u64))\n#fn use ((n #u64)) #u64 (#requires (#call positive ((n n)))) (#return n)\n#fn main () #u64 (#let n #u64 42u64) (#return (#if-valid (#call positive ((n n))) (#call use ((n n))) 0u64))\n";
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
    let source = "#fn main () #u64 (#let items (#array #u64 2) (#array-of (#array #u64 2) 20u64 42u64)) (#return (#index items 1usize))\n";
    wasm::check(source).unwrap();
    let error = wasm::compile(source).err().unwrap();
    assert_eq!(error.code, lim::DiagnosticCode::Codegen);
    assert!(error.message.contains("does not yet support"));
    assert!(wasm::check("#alias value = /tmp/private.lim::value\n")
        .unwrap_err()
        .message
        .contains("file imports"));
    assert!(wasm::compile(&" ".repeat(wasm::MAX_SOURCE_BYTES + 1)).is_err());
    assert!(wasm::compile("#fn main () #u64 (#return false)\n").is_err());
}

#[test]
fn syntax_diagnostics_keep_native_phase_codes_and_source_locations() {
    for (source, code) in [
        ("\"unfinished", lim::DiagnosticCode::Lex),
        ("#fn main", lim::DiagnosticCode::Parse),
    ] {
        let diagnostic = wasm::check(source).unwrap_err();
        assert_eq!(diagnostic.code, code);
        assert!(diagnostic.span.is_some());
        assert_eq!(diagnostic.source_text.as_deref(), Some(source));
    }
}

const PRINT_BINDING: &str = "#extern-fn #abi-c browser-print-u64 ((value #u64)) ()\n";

#[test]
fn compiled_loop_prints_through_the_single_explicit_host_import() {
    let source = format!(
        "{PRINT_BINDING}
#fn main () #u64
          (#for-range (number #u64) 1u64 11u64
            (#unsafe (#unsafe-call browser-print-u64 ((value number)))))
          (#unsafe (#unsafe-call browser-print-u64 ((value 18446744073709551615u64))))
          (#return 42u64)\n"
    );
    let module = wasm::compile(&source).unwrap();
    let scratch = support::Scratch::new("wasm-stdout");
    let path = scratch.path().join("program.wasm");
    fs::write(&path, module.bytes).unwrap();
    let script = "const fs=require('node:fs'); const module=new WebAssembly.Module(fs.readFileSync(process.argv[1])); const imports=WebAssembly.Module.imports(module); if(JSON.stringify(imports)!==JSON.stringify([{module:'lim',name:'print_u64',kind:'function'}]))throw Error('unexpected imports'); let stdout=''; const instance=new WebAssembly.Instance(module,{lim:{print_u64(value){stdout+=BigInt.asUintN(64,value)+'\\n';}}}); const value=instance.exports.main(); console.log(JSON.stringify({stdout,value:String(value)}));";
    let (status, out, error) = support::run(
        Command::new("node").arg("-e").arg(script).arg(path),
        Duration::from_secs(5),
        8192,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&error));
    assert_eq!(String::from_utf8(out).unwrap().trim(), "{\"stdout\":\"1\\n2\\n3\\n4\\n5\\n6\\n7\\n8\\n9\\n10\\n18446744073709551615\\n\",\"value\":\"42\"}");
}

#[test]
fn host_output_requires_the_exact_foreign_signature_and_unsafe_call_rules() {
    for binding in [
        "#extern-fn #abi-c browser-print-u64 ((value #i64)) ()\n",
        "#extern-fn #abi-c browser-print-u64 ((value #u64)) #u64\n",
        "#extern-fn #abi-c other-output ((value #u64)) ()\n",
    ] {
        let name = if binding.contains("other-output") {
            "other-output"
        } else {
            "browser-print-u64"
        };
        let source = format!(
            "{binding}\n#fn main () () (#unsafe (#unsafe-call {name} ((value 1)))) (#return ())\n"
        );
        let error = wasm::compile(&source)
            .err()
            .expect("an unrecognized host signature must fail");
        assert!(
            error.message.contains("browser-print-u64"),
            "{}",
            error.message
        );
        assert!(error.span.is_some());
    }
    assert!(wasm::compile(&format!(
        "{PRINT_BINDING}\n#fn main () () (#call browser-print-u64 ((value 1u64))) (#return ())\n"
    ))
    .is_err());
    assert!(wasm::compile(&format!("{PRINT_BINDING}\n#fn main () () (#unsafe-call browser-print-u64 ((value 1u64))) (#return ())\n")).is_err());
    assert!(
        wasm::compile("#alias print = ./main.lim::browser-print-u64\n")
            .err()
            .unwrap()
            .message
            .contains("file imports")
    );
    run("#fn browser-print-u64 ((value #u64)) #u64 (#return value)\n#fn main () #u64 (#return (#call browser-print-u64 ((value 42u64))))\n", "42");
}
