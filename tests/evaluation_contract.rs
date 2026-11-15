mod support;
use std::{process::Command, time::Duration};

#[test]
fn named_fields_calls_and_control_flow_follow_the_documented_evaluation_order() {
    let source = "#static trace (#atomic #u64) (#atomic-init #u64 0u64)
#struct Pair (#linear) ((first #u64) (second #u64))
#fn mark {
  #params = ((value #u64));
  #returns = #u64;
  #effects = ((#write-global trace)); #body = (
          (#let previous #u64 (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)))
          (#unsafe (#atomic-store (#borrow trace) (#u64::add-wrap (#u64::mul-wrap previous 10u64) value) #memory-relaxed))
          (#return value)
  );
}
#fn combine {
  #params = ((first #u64) (second #u64));
  #returns = #u64;
  #body = ( (#return (#u64::add-wrap (#u64::mul-wrap first 10u64) second))
  );
}
#fn flag {
  #params = ((value #bool));
  #returns = #bool;
  #body = ( (#return value)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of mark) (#write-global trace)); #body = (
          (#assert (#u64::eq (#call combine ((second (#call mark ((value 2u64)))) (first (#call mark ((value 1u64)))))) 12u64))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 21u64))
          (#unsafe (#atomic-store (#borrow trace) 0u64 #memory-relaxed))
          (#let pair Pair (#struct-literal Pair ((second (#call mark ((value 4u64)))) (first (#call mark ((value 3u64)))))))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 43u64)) (#forget pair)
          (#unsafe (#atomic-store (#borrow trace) 0u64 #memory-relaxed))
          (#let array (#array #u64 2) (#array-of (#array #u64 2) (#call mark ((value 5u64))) (#call mark ((value 6u64)))))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 56u64)) (#forget array)
          (#unsafe (#atomic-store (#borrow trace) 0u64 #memory-relaxed))
          (#assert (#bool::eq (#bool::and (#call flag ((value false))) (#block (#call mark ((value 9u64))) true)) false))
          (#assert (#bool::or (#call flag ((value true))) (#block (#call mark ((value 9u64))) false)))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 0u64))
          (#let selected #u64 (#match (#call mark ((value 1u64))) (#case (#literal #u64 1) (#call mark ((value 2u64)))) (#case _ 0u64)))
          (#assert (#u64::eq selected 2u64))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 12u64))
          (#return 42u64)\n  );\n}\n";
    let scratch = support::Scratch::new("evaluation-contract");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    };
    let cold = compile().unwrap();
    assert_eq!(
        cold,
        compile().unwrap(),
        "cache reuse must preserve observable effects"
    );
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &cold,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn returning_does_not_implicitly_destroy_an_unconsumed_owner() {
    let source = "#struct Owner (#linear) ((value #u64))\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let owner Owner (#struct-literal Owner ((value 42u64)))) (#return 0u64)\n  );\n}\n";
    let scratch = support::Scratch::new("explicit-destruction-contract");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(error.span.is_some(), "{error:?}");
}
